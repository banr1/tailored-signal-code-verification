/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAux -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat -- proof-setup: allow-public-import
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxBSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop

/-!
# `HookSat` Sibling of `CryptoBridgePlacedBudgetAux` (`CryptoBridgePlacedBudgetAuxSat`)

Proves the top-level `VmPreserved`-strengthened relocatable `subroutine_ok` contract
`expand_multi_info_placed_vm_ok_sat` (`GenericHkdf<Hmac<Sha256>>::expand_multi_info`, Block `53`,
`okmLen ∈ {64, 80}`, `info.length < 23`) under `[HkdfPlacedHooksBudgetSat C.F H]`
(`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat

open Arm64 ProofLib SepProp
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   extract_withLsCodeLoaded libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_8_eq readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt
   RW RunsTo TraceEq blkLib_53 blkLib_eq_53 blkPC_53 blkPl_53 expPlacedFakeB
   expPlacedFakeB_off_0 expandMultiInfoSpec finPlacedFakeB finPlacedFakeB_off_0
   hmacCoreAt isBlock_hmacCoreAt length_hmacWith
   ro_outside_rw_shared_lb rw_of_perm_eq zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPre ExpandSaved
   StateDone StateLoop StateLoopA2Placed StateLoopB StateLoopCPlaced StateLoopFin
   StateX1Placed StateX1b StateX2Placed StateX2r esp esp_aligned fin_side_conditions
   hkdfExpand_64_eq hkdfExpand_80_eq t1 t1_length t2 t2_length t3 t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (checkBlockNoMsrTpidrEl0 hmacCompressOnlyExcHooks)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm finalize_fixed_placed_runsToVm_sat lift_block_vm_compress_only
   stripS_hmacSt stripS_mem stripS_read64 stripS_readBytes)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxBSat
  (epilogue_raw_hmc iter_a1_hmc iter_a2_hmc iter_b_hmc iter_c_hmc
   iter_d_continue_hmc iter_d_done_hmc seg0_hmc seg1_hmc seg2a_hmc seg2b_hmc seg3_hmc)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksBudgetSat HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat (ExpandFrameS2)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## 1. Block `53` Checks, `ExpandPreBase`, and `stripS` / `unstrip` Helpers -/

private theorem blk53_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_53.text = true := by decide +kernel
private theorem blk53_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_53.text = true := by decide +kernel

@[local simp]
private theorem esp_setMem (s₀ : State) (m : Memory) : esp (s₀.setMem m) = esp s₀ := rfl

private theorem esp_stripS (kp : BitVec 64 → Bool) (s₀ : State) :
    esp (ProofLib.stripS kp s₀) = esp s₀ := by cases s₀; rfl

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

private theorem expandPre_stripS [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hpre : ExpandPre expPlacedFakeB F prk info infoPtr okmLen s₀) (kp : BitVec 64 → Bool) :
    ExpandPre expPlacedFakeB F prk info infoPtr okmLen (ProofLib.stripS kp s₀) := by
  have hr : ∀ r, (ProofLib.stripS kp s₀).readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  have hsp0 : (ProofLib.stripS kp s₀).sp = s₀.sp := by cases s₀; rfl
  exact
    { pc_eq := by cases s₀; exact hpre.pc_eq
      status := by cases s₀; exact hpre.status
      x3_eq := by rw [hr]; exact hpre.x3_eq
      prk_le := hpre.prk_le
      info_lt := hpre.info_lt
      okm_len := hpre.okm_len
      hmac_st := by rw [hr]; exact (stripS_hmacSt kp).mpr hpre.hmac_st
      info_ptr := by rw [hr, stripS_read64]; exact hpre.info_ptr
      info_len := by rw [hr, stripS_read64]; exact hpre.info_len
      info_bytes := by rw [stripS_readBytes]; exact hpre.info_bytes
      read_x0 := by rw [stripS_mem, hr]; exact stripExecOutside_readable kp s₀.mem _ _ hpre.read_x0
      read_x1 := by rw [stripS_mem, hr]; exact stripExecOutside_readable kp s₀.mem _ _ hpre.read_x1
      rw_x2 := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s₀.mem _ _ hpre.rw_x2
      rw_stack := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s₀.mem _ _ hpre.rw_stack
      disj_x2_stack := by rw [hr, hsp0]; exact hpre.disj_x2_stack
      disj_x0_stack := by rw [hr, hsp0]; exact hpre.disj_x0_stack
      disj_x0_x2 := by rw [hr]; exact hpre.disj_x0_x2
      disj_x1_stack := by rw [hr, hsp0]; exact hpre.disj_x1_stack
      disj_x1_x2 := by rw [hr]; exact hpre.disj_x1_x2
      out_info_stk := by rw [hsp0]; exact hpre.out_info_stk
      out_info_x2 := by rw [hr]; exact hpre.out_info_x2
      sp_aligned := by rw [hsp0]; exact hpre.sp_aligned }

private theorem stripS_expandSaved (kp : BitVec 64 → Bool) (s₀ s : State) :
    ExpandSaved (ProofLib.stripS kp s₀) (ProofLib.stripS kp s).mem ↔
    ExpandSaved s₀ s.mem := by
  have hesp : esp (ProofLib.stripS kp s₀) = esp s₀ := esp_stripS kp s₀
  have hr : ∀ r, (ProofLib.stripS kp s₀).readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  constructor <;> intro h <;> rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · simp only [hesp, stripS_read64, hr] at *
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hesp, stripS_read64, hr, *]

private theorem stripS_expandCommon_refl (kp : BitVec 64 → Bool) {okmLen : ℕ} {s₀ s : State}
    (hc : ExpandCommon okmLen (s₀.setMem s.mem) s) :
    ExpandCommon okmLen (ProofLib.stripS kp (s₀.setMem s.mem)) (ProofLib.stripS kp s) := by
  have hesp : esp (ProofLib.stripS kp (s₀.setMem s.mem)) = esp s₀ := by
    rw [esp_stripS, esp_setMem]
  have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem s.mem)).readReg64 r = s₀.readReg64 r :=
    fun _ => by cases s₀; rfl
  have hm_eq : (ProofLib.stripS kp (s₀.setMem s.mem)).mem = (ProofLib.stripS kp s).mem := by
    cases s₀; cases s; rfl
  exact
    { status := by cases s; exact hc.status
      sp_eq := by rw [hesp]; cases s; exact hc.sp_eq
      x29_eq := by rw [hesp]; cases s; exact hc.x29_eq
      x27_eq := by rw [hesp]; cases s; exact hc.x27_eq
      x20_eq := by rw [hr0]; cases s; exact hc.x20_eq
      m8_eq := by rw [hesp, stripS_read64, hr0]; exact hc.m8_eq
      m16_eq := by rw [hesp, stripS_read64]; exact hc.m16_eq
      saved := (stripS_expandSaved kp (s₀.setMem s.mem) s).mpr hc.saved
      frame := by
        unfold ExpandFrame
        rw [stripS_mem, show (s₀.setMem s.mem).mem = s.mem from rfl]
        exact Frame.refl _ _ }

private theorem unstrip_expandCommon {kp : BitVec 64 → Bool} {okmLen : ℕ} {s_ref sf : State}
    (hc : ExpandCommon okmLen (ProofLib.stripS kp s_ref) (ProofLib.stripS kp sf))
    (hperm : ∀ a, sf.mem.perm a = s_ref.mem.perm a) :
    ExpandCommon okmLen s_ref sf := by
  have hesp : esp (ProofLib.stripS kp s_ref) = esp s_ref := esp_stripS kp s_ref
  have hr0 : ∀ r, (ProofLib.stripS kp s_ref).readReg64 r = s_ref.readReg64 r :=
    fun _ => by cases s_ref; rfl
  have hsp0 : (ProofLib.stripS kp s_ref).sp = s_ref.sp := by cases s_ref; rfl
  rcases hc with ⟨hst, hsp, hx29, hx27, hx20, hm8, hm16, hsav, hfr⟩
  unfold ExpandFrame at hfr
  rw [stripS_mem, stripS_mem, hr0, hsp0] at hfr
  exact
    { status := by cases sf; exact hst
      sp_eq := by rw [hesp] at hsp; cases sf; exact hsp
      x29_eq := by rw [hesp] at hx29; cases sf; exact hx29
      x27_eq := by rw [hesp] at hx27; cases sf; exact hx27
      x20_eq := by rw [hr0] at hx20; cases sf; exact hx20
      m8_eq := by rw [hesp, stripS_read64, hr0] at hm8; exact hm8
      m16_eq := by rw [hesp, stripS_read64] at hm16; exact hm16
      saved := (stripS_expandSaved kp s_ref sf).mp hsav
      frame := unstrip_frame hfr hperm }

/-! ## 2. Multi-Block `RunsToVm` Assembly for Block `53` + Block `123` -/

private theorem runsTo_53_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop}
    (h : RunsTo ((blkPC_53).rebase (blkPl_53).base X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 53 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_53).rebase (blkPl_53).base X)]

private theorem unstrip_stateLoopCPlaced [LibsignalPlacement] {kp : BitVec 64 → Bool}
    {F : ShaState → List (BitVec 8) → ShaState} {prk info tPrev okmSoFar : List (BitVec 8)}
    {okmLen i rem dstOff : ℕ} {s_ref sf : State}
    (hq : StateLoopCPlaced F prk info tPrev okmSoFar okmLen i rem dstOff
      (ProofLib.stripS kp s_ref) (ProofLib.stripS kp sf))
    (hperm : ∀ a, sf.mem.perm a = s_ref.mem.perm a) :
    StateLoopCPlaced F prk info tPrev okmSoFar okmLen i rem dstOff s_ref sf := by
  have hesp : esp (ProofLib.stripS kp s_ref) = esp s_ref := esp_stripS kp s_ref
  have hr0 : ∀ r, (ProofLib.stripS kp s_ref).readReg64 r = s_ref.readReg64 r :=
    fun _ => by cases s_ref; rfl
  rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx19, hx21, hx22, hx23, hx24, hx26, hx28, hhmac, hokm⟩
  exact
    { pc_eq := by cases sf; exact hpc
      common := unstrip_expandCommon hcom hperm
      lr_eq := by cases sf; exact hlr
      x0_eq := by rw [hesp] at hx0; cases sf; exact hx0
      x1_eq := by rw [hesp] at hx1; cases sf; exact hx1
      x19_eq := by cases sf; exact hx19
      x21_eq := by rw [hr0] at hx21; cases sf; exact hx21
      x22_eq := by rw [hr0] at hx22; cases sf; exact hx22
      x23_eq := by cases sf; exact hx23
      x24_eq := by cases sf; exact hx24
      x26_eq := by cases sf; exact hx26
      x28_eq := by rw [hesp] at hx28; cases sf; exact hx28
      hmac_240 := by rw [hesp] at hhmac; exact (stripS_hmacSt kp).mp hhmac
      okm_pre := by rw [hr0, stripS_readBytes] at hokm; exact hokm }

private theorem fin1_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (hx : StateX2Placed C.F prk info okmLen (s₀.setMem m_ref) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 okmLen s₀ m_ref' ∧ m_ref' = s'.mem ∧
        StateX2r expPlacedFakeB C.F prk info okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases fin_side_conditions (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hx.pc_eq
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
  refine ((finalize_fixed_placed_runsToVm_sat (C := C) (H := H) hcl hfin_pre).of_other_block
    (i := 53) (j := 123) (by decide) (by decide) hcl).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, esp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, esp_setMem] at hfr
  obtain ⟨hf_s', hc'⟩ := expandCommon_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', rfl, ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩⟩

private theorem iter_fin_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf_ref : ExpandFrameS2 okmLen s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_ref) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 okmLen s₀ m_ref' ∧ m_ref' = s'.mem ∧
        StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases fin_side_conditions (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) okmLen :=
    ExpandFrame.rw_x2 (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hfin_pre : FinPre finPlacedFakeB C.F prk
      (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hx.pc_eq
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
  refine ((finalize_fixed_placed_runsToVm_sat (C := C) (H := H) hcl hfin_pre).of_other_block
    (i := 53) (j := 123) (by decide) (by decide) hcl).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
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
  exact ⟨s'.mem, hf_s', rfl, ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    hout, hokm'⟩⟩

private theorem ExpandPreBase.read_info_at [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : ExpandPreBase F prk info infoPtr okmLen s₀)
    (m : Memory) (hf : ExpandFrameS2 okmLen s₀ m) :
    m.Readable infoPtr info.length :=
  fun a ha => let ⟨hr, hlf⟩ := hb.read_info a ha; hf.2.2 a hr hlf

private theorem ExpandPreBase.disj_info [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : ExpandPreBase F prk info infoPtr okmLen s₀) :
    info.length = 0 ∨ DisjointRegions infoPtr info.length (s₀.sp - 640#64) 640 := by
  by_cases h0 : info.length = 0
  · exact Or.inl h0
  · have hinfo_lt := hb.pre.info_lt
    have h_mod : (BitVec.ofNat 64 (info.length - 1)).toNat = info.length - 1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h_i0 := hb.pre.out_info_stk infoPtr (by unfold InRegion; bv_omega)
    have h_in := hb.pre.out_info_stk (infoPtr + BitVec.ofNat 64 (info.length - 1))
      (by unfold InRegion; bv_omega)
    refine Or.inr ?_
    unfold DisjointRegions OutsideRegion at *
    bv_omega

private theorem expandSaved_setMem {s₀ : State} {m₁ m₂ m : Memory}
    (hs : ExpandSaved (s₀.setMem m₁) m) : ExpandSaved (s₀.setMem m₂) m := by
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  cases s₀
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private theorem expandCommon_setMem_self {okmLen : ℕ} {s₀ sl : State} {m : Memory}
    (hc : ExpandCommon okmLen (s₀.setMem m) sl) :
    ExpandCommon okmLen (s₀.setMem sl.mem) sl :=
  { status := hc.status
    sp_eq := hc.sp_eq
    x29_eq := hc.x29_eq
    x27_eq := hc.x27_eq
    x20_eq := hc.x20_eq
    m8_eq := hc.m8_eq
    m16_eq := hc.m16_eq
    saved := expandSaved_setMem hc.saved
    frame := Frame.refl sl.mem _ }

private theorem iter_abc_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameS2 okmLen s₀ s.mem)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 48 ∨ rem = 16)
    (hdst : dstOff ≤ okmLen)
    (hs : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff (s₀.setMem s.mem) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun sc =>
      ∃ m_c, ExpandFrameS2 okmLen s₀ m_c ∧
        StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_c) sc := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hpre_s := hb.at_mem s.mem hf
  have h_a : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff
        (s₀.setMem s.mem)) := by
    have hP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
        (StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem s.mem)) :=
      (iter_a1_hmc (C := C) (H := H) hpre_s hrem hdst hs).trans fun sa1 hsa1 =>
        iter_a2_hmc (C := C) (H := H) hpre_s ht_len hdst hsa1
    have hpre_strip := expandPre_stripS hpre_s kp
    have hesp_s : esp (ProofLib.stripS kp (s₀.setMem s.mem)) = esp s₀ := by
      rw [esp_stripS, esp_setMem]
    have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem s.mem)).readReg64 r = s₀.readReg64 r :=
      fun _ => by cases s₀; rfl
    have hs_strip : StateLoop expPlacedFakeB okmLen tPrev okmSoFar i rem dstOff
        (ProofLib.stripS kp (s₀.setMem s.mem)) (ProofLib.stripS kp s) :=
      { pc_eq := by cases s; exact hs.pc_eq
        common := stripS_expandCommon_refl kp hs.common
        x19_eq := by cases s; exact hs.x19_eq
        x22_eq := by rw [hr0]; cases s; exact hs.x22_eq
        x24_eq := by cases s; exact hs.x24_eq
        x26_eq := by cases s; exact hs.x26_eq
        x28_eq := by rw [hesp_s]; cases s; exact hs.x28_eq
        t_cache := by rw [hesp_s, stripS_readBytes]; exact hs.t_cache
        okm_pre := by rw [hr0, stripS_readBytes]; exact hs.okm_pre }
    have hQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
        (ProofLib.stripS kp s)
        (StateLoopA2Placed C.F prk info infoPtr tPrev okmSoFar okmLen i rem dstOff
          (ProofLib.stripS kp (s₀.setMem s.mem))) :=
      (iter_a1_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_strip hrem hdst hs_strip).trans
        fun sa1 hsa1 =>
        iter_a2_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_strip ht_len hdst hsa1
    refine lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
      (Pj := (blkPC_53).rebase (blkPl_53).base H)
      blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl
      (runsTo_53_to_bp hP) (runsTo_53_to_bp hQ)
      (fun _ h => h.common.status) (fun _ h => h.common.status) fun sf hvm hq => ?_
    rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx2, hx19, hx21, hx22, hx23, hx25, hx26, hx28, hhmac, hokm⟩
    exact
      { pc_eq := by cases sf; exact hpc
        common := unstrip_expandCommon hcom hvm.perm_eq
        lr_eq := by cases sf; exact hlr
        x0_eq := by rw [hesp_s] at hx0; cases sf; exact hx0
        x1_eq := by cases sf; exact hx1
        x2_eq := by cases sf; exact hx2
        x19_eq := by cases sf; exact hx19
        x21_eq := by cases sf; exact hx21
        x22_eq := by rw [hr0] at hx22; cases sf; exact hx22
        x23_eq := by cases sf; exact hx23
        x25_eq := by cases sf; exact hx25
        x26_eq := by cases sf; exact hx26
        x28_eq := by rw [hesp_s] at hx28; cases sf; exact hx28
        hmac_64 := by rw [hesp_s] at hhmac; exact (stripS_hmacSt kp).mp hhmac
        okm_pre := by rw [hr0, stripS_readBytes] at hokm; exact hokm }
  refine h_a.trans_full fun sa2 hsa2 hkfa => ?_
  refine (iter_b_hmc (C := C) (H := H) hH.memcpy hpre_s
    (hb.read_info_at s.mem hf) hb.disj_info ht_len hi hdst hsa2).trans_full fun sb hsb hkfb => ?_
  have hcl_b := (hcl.of_keepsFrozen hkfa).of_keepsFrozen hkfb
  have hf_b : ExpandFrameS2 okmLen s₀ sb.mem := hf.trans (S2Frame.of_frame hsb.common.frame)
  have hpre_b := hb.at_mem sb.mem hf_b
  have hsb' : StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
      (s₀.setMem sb.mem) sb :=
    { pc_eq := hsb.pc_eq
      common := expandCommon_setMem_self hsb.common
      x19_eq := hsb.x19_eq
      x22_eq := hsb.x22_eq
      x23_eq := hsb.x23_eq
      x24_eq := hsb.x24_eq
      x26_eq := hsb.x26_eq
      x28_eq := hsb.x28_eq
      hmac_64 := hsb.hmac_64
      okm_pre := hsb.okm_pre }
  have hP_c : RunsTo ((blkPC_53).rebase (blkPl_53).base H) sb
      (StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff (s₀.setMem sb.mem)) :=
    iter_c_hmc (C := C) (H := H) hpre_b hrem hdst hsb'
  have hpre_b_strip := expandPre_stripS hpre_b kp
  have hesp_b : esp (ProofLib.stripS kp (s₀.setMem sb.mem)) = esp s₀ := by
    rw [esp_stripS, esp_setMem]
  have hr0_b : ∀ r, (ProofLib.stripS kp (s₀.setMem sb.mem)).readReg64 r = s₀.readReg64 r :=
    fun _ => by cases s₀; rfl
  have hsb_strip : StateLoopB expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
      (ProofLib.stripS kp (s₀.setMem sb.mem)) (ProofLib.stripS kp sb) :=
    { pc_eq := by cases sb; exact hsb'.pc_eq
      common := stripS_expandCommon_refl kp hsb'.common
      x19_eq := by cases sb; exact hsb'.x19_eq
      x22_eq := by rw [hr0_b]; cases sb; exact hsb'.x22_eq
      x23_eq := by cases sb; exact hsb'.x23_eq
      x24_eq := by cases sb; exact hsb'.x24_eq
      x26_eq := by cases sb; exact hsb'.x26_eq
      x28_eq := by rw [hesp_b]; cases sb; exact hsb'.x28_eq
      hmac_64 := by rw [hesp_b]; exact (stripS_hmacSt kp).mpr hsb'.hmac_64
      okm_pre := by rw [hr0_b, stripS_readBytes]; exact hsb'.okm_pre }
  have hQ_c : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
      (ProofLib.stripS kp sb)
      (StateLoopCPlaced C.F prk info tPrev okmSoFar okmLen i rem dstOff
        (ProofLib.stripS kp (s₀.setMem sb.mem))) :=
    iter_c_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_b_strip hrem hdst hsb_strip
  exact (lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
    (Pj := (blkPC_53).rebase (blkPl_53).base H)
    blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl_b
    (runsTo_53_to_bp hP_c) (runsTo_53_to_bp hQ_c)
    (fun _ h => h.common.status) (fun _ h => h.common.status)
    (fun sf hvm hq => unstrip_stateLoopCPlaced hq hvm.perm_eq)).mono
    fun sc hsc => ⟨sb.mem, hf_b, hsc⟩

private theorem run_done_ep_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀)
    (hf : ExpandFrameS2 okmLen s₀ s.mem)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 32 ∨ rem = 16)
    (hdst : dstOff + rem = okmLen)
    (hokm : okmSoFar ++ (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).take rem =
              hkdfExpand C.F prk info okmLen)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar okmLen i rem dstOff
      (s₀.setMem s.mem) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand C.F prk info okmLen ∧
      ExpandFrameS2 okmLen s₀ sf.mem := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hpre_s := hb.at_mem s.mem hf
  refine (iter_d_done_hmc (C := C) (H := H) hH.memcpy hpre_s hi hrem hdst hokm hx).trans_full
    fun sd hsd hkfd => ?_
  have hcl_d := hcl.of_keepsFrozen hkfd
  have hf_d : ExpandFrameS2 okmLen s₀ sd.mem := hf.trans (S2Frame.of_frame hsd.common.frame)
  have hpre_d := hb.at_mem sd.mem hf_d
  have hsd' : StateDone expPlacedFakeB C.F prk info okmLen (s₀.setMem sd.mem) sd :=
    { pc_eq := hsd.pc_eq
      common := expandCommon_setMem_self hsd.common
      okm_all := hsd.okm_all }
  have hrunsP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) sd (fun sf =>
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand C.F prk info okmLen ∧
      ExpandFrame okmLen (s₀.setMem sd.mem) sf.mem) :=
    (epilogue_raw_hmc (C := C) (H := H) hpre_d hsd').mono
      fun sf ⟨hpc, hrun, hcs, hokm_f, hfr⟩ => ⟨hpc, hrun, ⟨hcs.1, hcs.2⟩, hokm_f, hfr⟩
  have hpre_d_strip := expandPre_stripS hpre_d kp
  have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 r = s₀.readReg64 r :=
    fun _ => by cases s₀; rfl
  have hsd_strip : StateDone expPlacedFakeB C.F prk info okmLen
      (ProofLib.stripS kp (s₀.setMem sd.mem)) (ProofLib.stripS kp sd) :=
    { pc_eq := by cases sd; exact hsd'.pc_eq
      common := stripS_expandCommon_refl kp hsd'.common
      okm_all := by rw [hr0, stripS_readBytes]; exact hsd'.okm_all }
  have hrunsQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
      (ProofLib.stripS kp sd) (fun sf' =>
        sf'.pc = (ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 .lr ∧
        sf'.status = .Running ∧
        CalleeSaved (ProofLib.stripS kp (s₀.setMem sd.mem)) sf' ∧
        sf'.mem.readBytes ((ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 .x2) okmLen =
          hkdfExpand C.F prk info okmLen ∧
        ExpandFrame okmLen (ProofLib.stripS kp (s₀.setMem sd.mem)) sf'.mem) :=
    (epilogue_raw_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_d_strip hsd_strip).mono
      fun sf' ⟨hpc, hrun, hcs, hokm_f, hfr⟩ => ⟨hpc, hrun, ⟨hcs.1, hcs.2⟩, hokm_f, hfr⟩
  refine (lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
    (Pj := (blkPC_53).rebase (blkPl_53).base H)
    blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl_d
    (runsTo_53_to_bp hrunsP) (runsTo_53_to_bp hrunsQ)
    (fun _ h => h.2.1) (fun _ h => h.2.1) ?_).mono fun sf ⟨hpc, hrun, hcs, hokm_f, hfr⟩ =>
      ⟨hpc, hrun, hcs, hokm_f, hf_d.trans (S2Frame.of_frame hfr)⟩
  intro sf hvm ⟨hpc', hrun', hcs', hokm', hfr'⟩
  have hsp0 : (ProofLib.stripS kp (s₀.setMem sd.mem)).sp = s₀.sp := by cases s₀; rfl
  unfold ExpandFrame at hfr'
  rw [stripS_mem, show (s₀.setMem sd.mem).mem = sd.mem from rfl, hr0, hsp0] at hfr'
  exact ⟨by rw [hr0] at hpc'; cases sf; exact hpc',
    by cases sf; exact hrun',
    ⟨by have h1 := hcs'.1; rw [hsp0] at h1; cases sf; exact h1,
     fun r hr_mem => by have h := hcs'.2 r hr_mem; rw [hr0] at h; cases sf; exact h⟩,
    by rw [hr0, stripS_readBytes] at hokm'; exact hokm',
    unstrip_frame hfr' hvm.perm_eq⟩

private theorem expand_multi_info_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : ExpandPreBase C.F prk info infoPtr okmLen s₀) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) okmLen = hkdfExpand C.F prk info okmLen ∧
      ExpandFrameS2 okmLen s₀ sf.mem := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : ExpandFrameS2 okmLen s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hpre₀ := hb.at_mem s₀.mem hf₀
  -- Piece 1a: `s₀ → StateX1Placed` (`seg0 ∘ seg1` in Block `53`)
  have h_run01 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX1Placed C.F prk info infoPtr okmLen (s₀.setMem s₀.mem)) := by
    have hP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
        (StateX1Placed C.F prk info infoPtr okmLen (s₀.setMem s₀.mem)) := by
      conv => arg 2; rw [← hs_id]
      exact (seg0_hmc (C := C) (H := H) hpre₀).trans fun s1 hs1 =>
        seg1_hmc (C := C) (H := H) hpre₀ hs1
    have hpre₀_strip := expandPre_stripS hpre₀ kp
    have hs_strip_id : ProofLib.stripS kp (s₀.setMem s₀.mem) = ProofLib.stripS kp s₀ := by
      rw [hs_id]
    have hQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
        (ProofLib.stripS kp s₀)
        (StateX1Placed C.F prk info infoPtr okmLen (ProofLib.stripS kp (s₀.setMem s₀.mem))) := by
      conv => arg 2; rw [← hs_strip_id]
      exact (seg0_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre₀_strip).trans
        fun s1 hs1 => seg1_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre₀_strip hs1
    refine lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
      (Pj := (blkPC_53).rebase (blkPl_53).base H)
      blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl₀
      (runsTo_53_to_bp hP) (runsTo_53_to_bp hQ)
      (fun _ h => h.common.status) (fun _ h => h.common.status) fun sf hvm hq => ?_
    have hesp : esp (ProofLib.stripS kp (s₀.setMem s₀.mem)) = esp s₀ := by
      rw [esp_stripS, esp_setMem]
    have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem s₀.mem)).readReg64 r = s₀.readReg64 r :=
      fun _ => by cases s₀; rfl
    rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx2, hx19, hx22, hx23, hx24, hx26, hhmac⟩
    exact
      { pc_eq := by cases sf; exact hpc
        common := unstrip_expandCommon hcom (fun a => by rw [hs_id]; exact hvm.perm_eq a)
        lr_eq := by cases sf; exact hlr
        x0_eq := by rw [hesp] at hx0; cases sf; exact hx0
        x1_eq := by cases sf; exact hx1
        x2_eq := by cases sf; exact hx2
        x19_eq := by cases sf; exact hx19
        x22_eq := by rw [hr0] at hx22; cases sf; exact hx22
        x23_eq := by cases sf; exact hx23
        x24_eq := by cases sf; exact hx24
        x26_eq := by cases sf; exact hx26
        hmac_64 := by rw [hesp] at hhmac; exact (stripS_hmacSt kp).mp hhmac }
  -- Piece 1b: `seg2a ∘ seg2b` (`StateX1Placed → StateX2Placed`)
  have h_run1 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (fun s4 => ∃ m0, ExpandFrameS2 okmLen s₀ m0 ∧
        StateX2Placed C.F prk info okmLen (s₀.setMem m0) s4) :=
    h_run01.trans_full fun s2 hs2 hkf2 =>
      (seg2a_hmc (C := C) (H := H) hH.memcpy hpre₀ hb.read_info hb.disj_info hs2).trans_full
        fun s3 hs3 hkf3 => by
          have hcl3 := (hcl₀.of_keepsFrozen hkf2).of_keepsFrozen hkf3
          have hf3 : ExpandFrameS2 okmLen s₀ s3.mem := hf₀.trans (S2Frame.of_frame hs3.common.frame)
          have hpre3 := hb.at_mem s3.mem hf3
          have hs3' : StateX1b expPlacedFakeB C.F prk info okmLen (s₀.setMem s3.mem) s3 :=
            { pc_eq := hs3.pc_eq
              common := expandCommon_setMem_self hs3.common
              x22_eq := hs3.x22_eq
              x23_eq := hs3.x23_eq
              x26_eq := hs3.x26_eq
              hmac_64 := hs3.hmac_64 }
          have hP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s3
              (StateX2Placed C.F prk info okmLen (s₀.setMem s3.mem)) :=
            seg2b_hmc (C := C) (H := H) hpre3 hs3'
          have hpre3_strip := expandPre_stripS hpre3 kp
          have hesp3 : esp (ProofLib.stripS kp (s₀.setMem s3.mem)) = esp s₀ := by
            rw [esp_stripS, esp_setMem]
          have hr03 : ∀ r, (ProofLib.stripS kp (s₀.setMem s3.mem)).readReg64 r = s₀.readReg64 r :=
            fun _ => by cases s₀; rfl
          have hs3_strip : StateX1b expPlacedFakeB C.F prk info okmLen
              (ProofLib.stripS kp (s₀.setMem s3.mem)) (ProofLib.stripS kp s3) :=
            { pc_eq := by cases s3; exact hs3'.pc_eq
              common := stripS_expandCommon_refl kp hs3'.common
              x22_eq := by rw [hr03]; cases s3; exact hs3'.x22_eq
              x23_eq := by cases s3; exact hs3'.x23_eq
              x26_eq := by cases s3; exact hs3'.x26_eq
              hmac_64 := by rw [hesp3]; exact (stripS_hmacSt kp).mpr hs3'.hmac_64 }
          have hQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
              (ProofLib.stripS kp s3)
              (StateX2Placed C.F prk info okmLen (ProofLib.stripS kp (s₀.setMem s3.mem))) :=
            seg2b_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre3_strip hs3_strip
          refine (lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
            (Pj := (blkPC_53).rebase (blkPl_53).base H)
            blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl3
            (runsTo_53_to_bp hP) (runsTo_53_to_bp hQ)
            (fun _ h => h.common.status) (fun _ h => h.common.status) fun sf hvm hq => ?_).mono
            fun s4 hs4 => ⟨s3.mem, hf3, hs4⟩
          rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx22, hx23, hx26, hhmac⟩
          exact
            { pc_eq := by cases sf; exact hpc
              common := unstrip_expandCommon hcom hvm.perm_eq
              lr_eq := by cases sf; exact hlr
              x0_eq := by rw [hesp3] at hx0; cases sf; exact hx0
              x1_eq := by rw [hesp3] at hx1; cases sf; exact hx1
              x22_eq := by rw [hr03] at hx22; cases sf; exact hx22
              x23_eq := by cases sf; exact hx23
              x26_eq := by cases sf; exact hx26
              hmac_240 := by rw [hesp3] at hhmac; exact (stripS_hmacSt kp).mp hhmac }
  -- Piece 2: `fin1` (`finalize_fixed` #1 in Block `123`)
  have h_after_fin1 := h_run1.trans_full fun s4 ⟨m0, hf0, hs4⟩ hkf4 =>
    fin1_placed_runsToVm_sat (C := C) (H := H) (hcl₀.of_keepsFrozen hkf4) hb hf0 hs4
  -- Piece 3: `seg3 ∘ iter_a1 ∘ iter_a2 ∘ iter_b ∘ iter_c` (`s5 → StateLoopCPlaced` for `i = 1`)
  have h_to_fin2 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (fun s6c => ∃ m1, ExpandFrameS2 okmLen s₀ m1 ∧
        StateLoopCPlaced C.F prk info (t1 C.F prk info) (t1 C.F prk info)
          okmLen 1 (okmLen - 32) 32 (s₀.setMem m1) s6c) :=
    h_after_fin1.trans_full fun s5 ⟨m1, hf1, hm1_eq, hs5⟩ hkf5 => by
      subst hm1_eq
      have hcl5 := hcl₀.of_keepsFrozen hkf5
      have hpre5 := hb.at_mem s5.mem hf1
      have hrem1 : okmLen - 32 = 32 ∨ okmLen - 32 = 48 ∨ okmLen - 32 = 16 := by
        rcases hb.pre.okm_len with rfl | rfl <;> simp
      have hdst1 : 32 ≤ okmLen := by rcases hb.pre.okm_len with rfl | rfl <;> decide
      refine (seg3_hmc (C := C) (H := H) hH.memcpy hpre5 hs5).trans_full fun sl hsl hkfl => ?_
      have hf_l : ExpandFrameS2 okmLen s₀ sl.mem := hf1.trans (S2Frame.of_frame hsl.common.frame)
      have hsl' : StateLoop expPlacedFakeB okmLen (t1 C.F prk info) (t1 C.F prk info)
          1 (okmLen - 32) 32 (s₀.setMem sl.mem) sl :=
        { pc_eq := hsl.pc_eq
          common := expandCommon_setMem_self hsl.common
          x19_eq := hsl.x19_eq
          x22_eq := hsl.x22_eq
          x24_eq := hsl.x24_eq
          x26_eq := hsl.x26_eq
          x28_eq := hsl.x28_eq
          t_cache := hsl.t_cache
          okm_pre := hsl.okm_pre }
      exact iter_abc_placed_runsToVm_sat (C := C) (H := H) (hcl5.of_keepsFrozen hkfl)
        hb hf_l (t1_length C.F prk info) (Or.inl rfl) hrem1 hdst1 hsl'
  -- Piece 4: `iter_fin` #1 (`finalize_fixed` #2 in Block `123`) & branch on `okmLen ∈ {64, 80}`
  refine h_to_fin2.trans_full fun s6c ⟨m1, hf1, hs6c⟩ hkf6 => ?_
  have hcl6 := hcl₀.of_keepsFrozen hkf6
  rcases hb.pre.okm_len with rfl | rfl
  · -- `okmLen = 64`
    have hfin2 := iter_fin_placed_runsToVm_sat (C := C) (H := H) hcl6 hb hf1
      (t1_length C.F prk info) (by decide) hs6c
    refine hfin2.trans_full fun s7 ⟨m2, hf2, hm2_eq, hs7⟩ hkf7 => ?_
    subst hm2_eq
    have hokm64 : t1 C.F prk info ++ (hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8])).take 32 =
        hkdfExpand C.F prk info 64 := by
      rw [show hmacWith C.F prk (t1 C.F prk info ++ info ++ [2#8]) = t2 C.F prk info from rfl,
          List.take_of_length_le (by rw [t2_length]), hkdfExpand_64_eq]
    exact run_done_ep_vm (C := C) (H := H) (hcl6.of_keepsFrozen hkf7) hb hf2
      (Or.inl rfl) (Or.inl rfl) rfl hokm64 hs7
  · -- `okmLen = 80`
    have hfin2 := iter_fin_placed_runsToVm_sat (C := C) (H := H) hcl6 hb hf1
      (t1_length C.F prk info) (by decide) hs6c
    have h_to_fin3 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s6c
        (fun s8c => ∃ m2, ExpandFrameS2 80 s₀ m2 ∧
          StateLoopCPlaced C.F prk info (t2 C.F prk info)
            (t1 C.F prk info ++ t2 C.F prk info) 80 2 16 64 (s₀.setMem m2) s8c) :=
      hfin2.trans_full fun s7 ⟨m2, hf2, hm2_eq, hs7⟩ hkf7 => by
        subst hm2_eq
        have hcl7 := hcl6.of_keepsFrozen hkf7
        have hpre7 := hb.at_mem s7.mem hf2
        refine (iter_d_continue_hmc (C := C) (H := H) hH.memcpy
          (tNext := t2 C.F prk info) hpre7 rfl (by decide) rfl hs7).trans_full
          fun s8 hs8 hkf8 => ?_
        have hf8 : ExpandFrameS2 80 s₀ s8.mem := hf2.trans (S2Frame.of_frame hs8.common.frame)
        have hs8' : StateLoop expPlacedFakeB 80 (t2 C.F prk info)
            (t1 C.F prk info ++ t2 C.F prk info) 2 16 64 (s₀.setMem s8.mem) s8 :=
          { pc_eq := hs8.pc_eq
            common := expandCommon_setMem_self hs8.common
            x19_eq := hs8.x19_eq
            x22_eq := hs8.x22_eq
            x24_eq := hs8.x24_eq
            x26_eq := hs8.x26_eq
            x28_eq := hs8.x28_eq
            t_cache := hs8.t_cache
            okm_pre := hs8.okm_pre }
        exact iter_abc_placed_runsToVm_sat (C := C) (H := H) (hcl7.of_keepsFrozen hkf8)
          hb hf8 (t2_length C.F prk info) (Or.inr rfl) (Or.inr (Or.inr rfl)) (by decide) hs8'
    refine h_to_fin3.trans_full fun s8c ⟨m2, hf2, hs8c⟩ hkf8 => ?_
    have hcl8 := hcl6.of_keepsFrozen hkf8
    have hfin3 := iter_fin_placed_runsToVm_sat (C := C) (H := H) hcl8 hb hf2
      (t2_length C.F prk info) (by decide) hs8c
    refine hfin3.trans_full fun s9 ⟨m3, hf3, hm3_eq, hs9⟩ hkf9 => ?_
    subst hm3_eq
    have hokm80 : (t1 C.F prk info ++ t2 C.F prk info) ++
        (hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8])).take 16 =
        hkdfExpand C.F prk info 80 := by
      rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
          hkdfExpand_80_eq]
    exact run_done_ep_vm (C := C) (H := H) (hcl8.of_keepsFrozen hkf9) hb hf3
      (Or.inr rfl) (Or.inr rfl) rfl hokm80 hs9

/-! ## 4. Top-Level `expand_multi_info_placed_vm_ok_sat` Contract -/

/-- `HookSat` sibling of `CryptoBridgePlacedBudgetAux.expand_multi_info_placed_vm_ok`:
relocatable `subroutine_ok` with `VmPreserved` for
`GenericHkdf<Hmac<Sha256>>::expand_multi_info` (Block `53`, `64` B and `80` B) under
`[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem expand_multi_info_placed_vm_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactBudgetSat C.F H] :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
      (withLsCodeLoaded lsmpl (withVmPreserved (expandMultiInfoSpec C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [withVmPreserved, expandMultiInfoSpec] at hpre
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
  have hb_hdr : IsBlock
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length))
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
  have hsep_hdr_stk : s0.mem ⊨
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA x.okmLen ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 x.info.length)) ∗
      (memRegion x.okmA x.okmLen ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
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
      read_info := fun a ha =>
        ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩ }
  intro hL0
  obtain ⟨sf, hsteps, hvm, htr, hv, ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    expand_multi_info_placed_runsToVm_sat (C := C) (H := H) hcl hb_base hL0
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee ⟨htr, hv⟩⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  unfold ExpandFrameS2 at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info x.okmLen).length = x.okmLen := by
    rcases hokm_len with h64 | h80
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h80, hkdfExpand_80_eq]; simp [t1_length, t2_length, t3_length]
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

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
