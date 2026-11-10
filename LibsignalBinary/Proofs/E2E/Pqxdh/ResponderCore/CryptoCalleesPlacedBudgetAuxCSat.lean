/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat -- proof-setup: allow-public-import
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxBSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedA
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandBlock1
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop

/-!
# `HookSat` Sibling of `CryptoCalleesPlacedBudgetAux`, Part C (`CryptoCalleesPlacedBudgetAuxCSat`)

Proves the `VmPreserved`-strengthened relocatable `subroutine_ok` contract
`expand_multi_info_96_46_placed_vm_ok_sat` (`GenericHkdf<Hmac<Sha256>>::expand_multi_info`,
Block `53`, `okmLen = 96`, `info.length = 46`) under `[HkdfPlacedHooksBudgetSat C.F H]`
(`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxCSat

open Arm64 ProofLib SepProp
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   extract_withLsCodeLoaded libsignalSessionLib lsmpl withLsCodeLoaded)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ExpandPre96_46 FinGenPre StateLoopA2_96Placed StateLoopB1_96Placed StateLoopB2_96Placed
   StateLoopB_96 StateLoopC_96Placed expandMultiInfo96_46Spec hkdfExpand_96_eq)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_8_eq)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt
   RW RunsTo TraceEq blkLib_53 blkLib_eq_53 blkPC_53 blkPl_53 expPlacedFakeB
   expPlacedFakeB_off_0 expandMultiInfoStack finPlacedFakeB finPlacedFakeB_off_0
   finalizeFixedStack hmacCoreAt isBlock_hmacCoreAt
   ro_outside_rw_shared_lb)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPost ExpandSaved
   StateDone StateLoop StateLoopFin StateX1Placed StateX1b
   StateX2Placed StateX2r esp esp_aligned esp_eq_add
   t1 t1_length t2 t2_length t3 t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (checkBlockNoMsrTpidrEl0 hmacCompressOnlyExcHooks hmacCompressOnlyExcHooks_compress)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm finalize_fixed_placed_runsToVm_sat lift_block_vm_compress_only
   stripS_hmacSt stripS_mem stripS_read64 stripS_read8 stripS_readBytes)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
  (finalize_fixed_gen_placed_runsToVm_sat stripS_hmacStGen)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxBSat
  (iter_a1_96_hmc iter_a2_96_hmc iter_b1_96_hmc iter_b2_96_hc256 iter_b3_96_hmc
   iter_c_96_hmc iter_d_continue_96_hmc iter_d_done_96_hmc
   seg0_96_hmc seg1_96_hmc seg2a_96_hmc seg2b_96_hmc seg3_96_hmc)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat (ExpandFrameS2)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## 1. Block `53` Checks, `ExpandPre96_46Base`, and `stripS` / `unstrip` Helpers -/

private theorem blk53_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_53.text = true := by decide +kernel
private theorem blk53_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_53.text = true := by decide +kernel

@[local simp]
private theorem esp_setMem (s₀ : State) (m : Memory) : esp (s₀.setMem m) = esp s₀ := rfl

private theorem esp_stripS (kp : BitVec 64 → Bool) (s₀ : State) :
    esp (ProofLib.stripS kp s₀) = esp s₀ := by cases s₀; rfl

private structure ExpandPre96_46Base [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
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

private theorem expandSaved_setMem {s₀ : State} {m₁ m₂ m : Memory}
    (hs : ExpandSaved (s₀.setMem m₁) m) : ExpandSaved (s₀.setMem m₂) m := by
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  cases s₀
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private theorem expandCommon96_reset_of_fin [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {prk info : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s s' : State} {m_ref : Memory}
    (hb : ExpandPre96_46Base F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (hc : ExpandCommon 96 (s₀.setMem m_ref) s)
    (hstat : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem
      [(esp s₀ + 208#64, 32), (esp s₀ + 240#64, 144), (esp s₀ - 144#64, 144)]) :
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

private theorem expandPre96_46_stripS [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46 expPlacedFakeB F prk info infoPtr s₀) (kp : BitVec 64 → Bool) :
    ExpandPre96_46 expPlacedFakeB F prk info infoPtr (ProofLib.stripS kp s₀) := by
  have hr : ∀ r, (ProofLib.stripS kp s₀).readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  have hsp0 : (ProofLib.stripS kp s₀).sp = s₀.sp := by cases s₀; rfl
  exact
    { pc_eq := by cases s₀; exact hpre.pc_eq
      status := by cases s₀; exact hpre.status
      x3_eq := by rw [hr]; exact hpre.x3_eq
      prk_le := hpre.prk_le
      info_len_eq := hpre.info_len_eq
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

private theorem epilogue_96_raw_hmc [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
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

/-! ## 2. Multi-Block `RunsToVm` Assembly for Block `53` (`96` B) + Block `123` -/

private theorem runsTo_53_to_bp [LibsignalPlacement] {X : LibsignalHooks}
    {s : State} {P : State → Prop}
    (h : RunsTo ((blkPC_53).rebase (blkPl_53).base X) s P) :
    RunsTo (libsignalSessionLib.blockProgram lsmpl 53 X) s P := by
  rwa [← IsLsBlockProg.eq_blockProgram (prog := (blkPC_53).rebase (blkPl_53).base X)]

private theorem unstrip_stateLoopC_96Placed [LibsignalPlacement] {kp : BitVec 64 → Bool}
    {F : ShaState → List (BitVec 8) → ShaState} {prk info tPrev okmSoFar : List (BitVec 8)}
    {i rem dstOff : ℕ} {s_ref sf : State}
    (hq : StateLoopC_96Placed F prk info tPrev okmSoFar i rem dstOff
      (ProofLib.stripS kp s_ref) (ProofLib.stripS kp sf))
    (hperm : ∀ a, sf.mem.perm a = s_ref.mem.perm a) :
    StateLoopC_96Placed F prk info tPrev okmSoFar i rem dstOff s_ref sf := by
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
      hmac_240 := by rw [hesp] at hhmac; exact (stripS_hmacStGen kp).mp hhmac
      okm_pre := by rw [hr0, stripS_readBytes] at hokm; exact hokm }

private theorem ExpandPre96_46Base.read_info_at [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hb : ExpandPre96_46Base F prk info infoPtr s₀)
    (m : Memory) (hf : ExpandFrameS2 96 s₀ m) :
    m.Readable infoPtr 46 :=
  fun a ha => let ⟨hr, hlf⟩ := hb.read_info a ha; hf.2.2 a hr hlf

private theorem expandCommon_setMem_self {okmLen : ℕ} {s₀ sl : State} {m : Memory}
    (hc : ExpandCommon okmLen (s₀.setMem m) sl) :
    ExpandCommon okmLen (s₀.setMem sl.mem) sl :=
  { status := hc.status, sp_eq := hc.sp_eq, x29_eq := hc.x29_eq,
    x27_eq := hc.x27_eq, x20_eq := hc.x20_eq, m8_eq := hc.m8_eq, m16_eq := hc.m16_eq,
    saved := expandSaved_setMem hc.saved, frame := Frame.refl sl.mem _ }

private theorem expandCommon_trans_frame {okmLen : ℕ} {s₀ sf : State} {m₀ m₁ : Memory}
    (hf01 : ExpandFrame okmLen (s₀.setMem m₀) m₁)
    (hc : ExpandCommon okmLen (s₀.setMem m₁) sf) :
    ExpandCommon okmLen (s₀.setMem m₀) sf :=
  { status := hc.status, sp_eq := hc.sp_eq, x29_eq := hc.x29_eq,
    x27_eq := hc.x27_eq, x20_eq := hc.x20_eq, m8_eq := hc.m8_eq, m16_eq := hc.m16_eq,
    saved := expandSaved_setMem hc.saved, frame := hf01.trans hc.frame }

private theorem fin1_96_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (hx : StateX2Placed C.F prk info 96 (s₀.setMem m_ref) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 96 s₀ m_ref' ∧ m_ref' = s'.mem ∧
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
  refine ((finalize_fixed_placed_runsToVm_sat (C := C) (H := H) hcl hfin_pre).of_other_block
    (i := 53) (j := 123) (by decide) (by decide) hcl).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, esp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, esp_setMem] at hfr
  obtain ⟨hf_s', hc'⟩ := expandCommon96_reset_of_fin hb hf_ref hx.common hrun' hcs hfr
  exact ⟨s'.mem, hf_s', rfl, ⟨by rw [hpc']; simp only [arm64_norm], hc',
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩⟩

private theorem iter_fin_96_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf_ref : ExpandFrameS2 96 s₀ m_ref)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff (s₀.setMem m_ref) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun s' =>
      ∃ m_ref', ExpandFrameS2 96 s₀ m_ref' ∧ m_ref' = s'.mem ∧
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
  refine ((finalize_fixed_gen_placed_runsToVm_sat (C := C) (H := H) hcl hfin_pre).of_other_block
    (i := 53) (j := 123) (by decide) (by decide) hcl).mono fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
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
  exact ⟨s'.mem, hf_s', rfl, ⟨by rw [hpc']; simp only [arm64_norm],
    hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans (by rw [hmin]; exact hx.x21_eq),
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans (by rw [hmin]; exact hx.x23_eq),
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans (by rw [hmin]; exact hx.x26_eq),
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩⟩

private theorem run_iter_to_loopC_96_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf : ExpandFrameS2 96 s₀ s.mem)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff (s₀.setMem s.mem) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff (s₀.setMem s.mem)) := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hc256Q := hmacCompressOnlyExcHooks_compress C.F H
  have hpre_s := hb.at_mem s.mem hf
  -- Step A: `s → StateLoopA2_96Placed` (`iter_a1 ∘ iter_a2`)
  have h_a : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff (s₀.setMem s.mem)) := by
    have hP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
        (StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff (s₀.setMem s.mem)) :=
      (iter_a1_96_hmc (C := C) (H := H) hpre_s hrem hdst hx).trans fun _ hs1 =>
        iter_a2_96_hmc (C := C) (H := H) hpre_s ht_len hrem hdst hs1
    have hpre_strip := expandPre96_46_stripS hpre_s kp
    have hesp_s : esp (ProofLib.stripS kp (s₀.setMem s.mem)) = esp s₀ := by
      rw [esp_stripS, esp_setMem]
    have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem s.mem)).readReg64 r = s₀.readReg64 r :=
      fun _ => by cases s₀; rfl
    have hx_strip : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff
        (ProofLib.stripS kp (s₀.setMem s.mem)) (ProofLib.stripS kp s) :=
      { pc_eq := by cases s; exact hx.pc_eq
        common := stripS_expandCommon_refl kp hx.common
        x19_eq := by cases s; exact hx.x19_eq
        x22_eq := by rw [hr0]; cases s; exact hx.x22_eq
        x24_eq := by cases s; exact hx.x24_eq
        x26_eq := by cases s; exact hx.x26_eq
        x28_eq := by rw [hesp_s]; cases s; exact hx.x28_eq
        t_cache := by rw [hesp_s, stripS_readBytes]; exact hx.t_cache
        okm_pre := by rw [hr0, stripS_readBytes]; exact hx.okm_pre }
    have hQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
        (ProofLib.stripS kp s)
        (StateLoopA2_96Placed C.F prk tPrev okmSoFar infoPtr i rem dstOff
          (ProofLib.stripS kp (s₀.setMem s.mem))) :=
      (iter_a1_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_strip hrem hdst hx_strip).trans
        fun _ hs1 =>
        iter_a2_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_strip ht_len hrem hdst hs1
    refine lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
      (Pj := (blkPC_53).rebase (blkPl_53).base H)
      blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl
      (runsTo_53_to_bp hP) (runsTo_53_to_bp hQ)
      (fun _ h => h.common.status) (fun _ h => h.common.status) fun sf hvm hq => ?_
    rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx2, hx19, hx22, hx23, hx26, hx28, hm0, hhmac, hokm⟩
    exact
      { pc_eq := by cases sf; exact hpc
        common := unstrip_expandCommon hcom hvm.perm_eq
        lr_eq := by cases sf; exact hlr
        x0_eq := by rw [hesp_s] at hx0; cases sf; exact hx0
        x1_eq := by cases sf; exact hx1
        x2_eq := by cases sf; exact hx2
        x19_eq := by cases sf; exact hx19
        x22_eq := by rw [hr0] at hx22; cases sf; exact hx22
        x23_eq := by cases sf; exact hx23
        x26_eq := by cases sf; exact hx26
        x28_eq := by cases sf; exact hx28
        m0_eq := by rw [hesp_s, stripS_read64] at hm0; exact hm0
        hmac_64 := by rw [hesp_s] at hhmac; exact (stripS_hmacSt kp).mp hhmac
        okm_pre := by rw [hr0, stripS_readBytes] at hokm; exact hokm }
  -- Step B1: `sa2 → StateLoopB1_96Placed` (`iter_b1_96_hmc`)
  refine h_a.trans_full fun sa2 hsa2 hkfa => ?_
  refine (iter_b1_96_hmc (C := C) (H := H) hH.memcpy hpre_s (hb.read_info_at s.mem hf)
    ht_len hdst hsa2).trans_full fun sb1 hsb1 hkfb1 => ?_
  have hcl_b1 := (hcl.of_keepsFrozen hkfa).of_keepsFrozen hkfb1
  have hf_b1 : ExpandFrameS2 96 s₀ sb1.mem := hf.trans (S2Frame.of_frame hsb1.common.frame)
  have hpre_b1 := hb.at_mem sb1.mem hf_b1
  have hsb1' : StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff
      (s₀.setMem sb1.mem) sb1 :=
    { pc_eq := hsb1.pc_eq, common := expandCommon_setMem_self hsb1.common,
      lr_eq := hsb1.lr_eq, x0_eq := hsb1.x0_eq, x1_eq := hsb1.x1_eq, x2_eq := hsb1.x2_eq,
      x19_eq := hsb1.x19_eq, x22_eq := hsb1.x22_eq, x23_eq := hsb1.x23_eq,
      x26_eq := hsb1.x26_eq, x28_eq := hsb1.x28_eq, m0_eq := hsb1.m0_eq,
      blk_64 := hsb1.blk_64, ist_128 := hsb1.ist_128, cnt1_160 := hsb1.cnt1_160,
      ost_168 := hsb1.ost_168, cnt2_200 := hsb1.cnt2_200, okm_pre := hsb1.okm_pre }
  -- Step B2: `sb1 → StateLoopB2_96Placed` (`iter_b2_96_hc256` with `compress256`)
  have h_b2 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) sb1
      (StateLoopB2_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff
        (s₀.setMem sb1.mem)) := by
    have hP_b2 := iter_b2_96_hc256 (C := C) (H := H) hH.compress256 hpre_b1 ht_len hdst hsb1'
    have hpre_b1_strip := expandPre96_46_stripS hpre_b1 kp
    have hesp_b1 : esp (ProofLib.stripS kp (s₀.setMem sb1.mem)) = esp s₀ := by
      rw [esp_stripS, esp_setMem]
    have hr0_b1 : ∀ r, (ProofLib.stripS kp (s₀.setMem sb1.mem)).readReg64 r = s₀.readReg64 r :=
      fun _ => by cases s₀; rfl
    have hsb1_strip : StateLoopB1_96Placed C.F prk info tPrev okmSoFar infoPtr i rem dstOff
        (ProofLib.stripS kp (s₀.setMem sb1.mem)) (ProofLib.stripS kp sb1) :=
      { pc_eq := by cases sb1; exact hsb1'.pc_eq
        common := stripS_expandCommon_refl kp hsb1'.common
        lr_eq := by cases sb1; exact hsb1'.lr_eq
        x0_eq := by rw [hesp_b1]; cases sb1; exact hsb1'.x0_eq
        x1_eq := by rw [hesp_b1]; cases sb1; exact hsb1'.x1_eq
        x2_eq := by cases sb1; exact hsb1'.x2_eq
        x19_eq := by cases sb1; exact hsb1'.x19_eq
        x22_eq := by rw [hr0_b1]; cases sb1; exact hsb1'.x22_eq
        x23_eq := by cases sb1; exact hsb1'.x23_eq
        x26_eq := by cases sb1; exact hsb1'.x26_eq
        x28_eq := by cases sb1; exact hsb1'.x28_eq
        m0_eq := by rw [hesp_b1, stripS_read64]; exact hsb1'.m0_eq
        blk_64 := by rw [hesp_b1, stripS_readBytes]; exact hsb1'.blk_64
        ist_128 := by rw [hesp_b1, stripS_readBytes]; exact hsb1'.ist_128
        cnt1_160 := by rw [hesp_b1, stripS_read64]; exact hsb1'.cnt1_160
        ost_168 := by rw [hesp_b1, stripS_readBytes]; exact hsb1'.ost_168
        cnt2_200 := by rw [hesp_b1, stripS_read64]; exact hsb1'.cnt2_200
        okm_pre := by rw [hr0_b1, stripS_readBytes]; exact hsb1'.okm_pre }
    have hQ_b2 := iter_b2_96_hc256 (C := C) (H := hmacCompressOnlyExcHooks C.F H)
      hc256Q hpre_b1_strip ht_len hdst hsb1_strip
    refine lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
      (Pj := (blkPC_53).rebase (blkPl_53).base H)
      blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl_b1
      (runsTo_53_to_bp hP_b2) (runsTo_53_to_bp hQ_b2)
      (fun _ h => h.common.status) (fun _ h => h.common.status) fun sf hvm hq => ?_
    rcases hq with ⟨hpc, hcom, hlr, hx0, hx1, hx2, hx19, hx22, hx23, hx26, hpos, hist, hc1, host, hc2, hokm⟩
    exact
      { pc_eq := by cases sf; exact hpc
        common := unstrip_expandCommon hcom hvm.perm_eq
        lr_eq := by cases sf; exact hlr
        x0_eq := by rw [hesp_b1] at hx0; cases sf; exact hx0
        x1_eq := by cases sf; exact hx1
        x2_eq := by cases sf; exact hx2
        x19_eq := by cases sf; exact hx19
        x22_eq := by rw [hr0_b1] at hx22; cases sf; exact hx22
        x23_eq := by cases sf; exact hx23
        x26_eq := by cases sf; exact hx26
        pos_127 := by rw [hesp_b1, stripS_read8] at hpos; exact hpos
        ist_128 := by rw [hesp_b1, stripS_readBytes] at hist; exact hist
        cnt1_160 := by rw [hesp_b1, stripS_read64] at hc1; exact hc1
        ost_168 := by rw [hesp_b1, stripS_readBytes] at host; exact host
        cnt2_200 := by rw [hesp_b1, stripS_read64] at hc2; exact hc2
        okm_pre := by rw [hr0_b1, stripS_readBytes] at hokm; exact hokm }
  -- Step B3 + Step C: `sb2 → StateLoopB_96 → StateLoopC_96Placed`
  refine h_b2.trans_full fun sb2 hsb2 hkfb2 => ?_
  refine (iter_b3_96_hmc (C := C) (H := H) hH.memcpy hpre_b1 (hb.read_info_at sb1.mem hf_b1)
    ht_len hi hdst hsb2).trans_full fun sb3 hsb3 hkfb3 => ?_
  have hcl_b3 := (hcl_b1.of_keepsFrozen hkfb2).of_keepsFrozen hkfb3
  have hf_s_b3 : ExpandFrame 96 (s₀.setMem s.mem) sb3.mem :=
    hsb1.common.frame.trans hsb3.common.frame
  have hf_b3 : ExpandFrameS2 96 s₀ sb3.mem := hf.trans (S2Frame.of_frame hf_s_b3)
  have hpre_b3 := hb.at_mem sb3.mem hf_b3
  have hsb3' : StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff
      (s₀.setMem sb3.mem) sb3 :=
    { pc_eq := hsb3.pc_eq, common := expandCommon_setMem_self hsb3.common,
      x19_eq := hsb3.x19_eq, x22_eq := hsb3.x22_eq, x23_eq := hsb3.x23_eq,
      x24_eq := hsb3.x24_eq, x26_eq := hsb3.x26_eq, x28_eq := hsb3.x28_eq,
      hmac_64 := hsb3.hmac_64, okm_pre := hsb3.okm_pre }
  have hP_c := iter_c_96_hmc (C := C) (H := H) hpre_b3 hrem hdst hsb3'
  have hpre_b3_strip := expandPre96_46_stripS hpre_b3 kp
  have hesp_b3 : esp (ProofLib.stripS kp (s₀.setMem sb3.mem)) = esp s₀ := by
    rw [esp_stripS, esp_setMem]
  have hr0_b3 : ∀ r, (ProofLib.stripS kp (s₀.setMem sb3.mem)).readReg64 r = s₀.readReg64 r :=
    fun _ => by cases s₀; rfl
  have hsb3_strip : StateLoopB_96 expPlacedFakeB C.F prk info tPrev okmSoFar i rem dstOff
      (ProofLib.stripS kp (s₀.setMem sb3.mem)) (ProofLib.stripS kp sb3) :=
    { pc_eq := by cases sb3; exact hsb3'.pc_eq
      common := stripS_expandCommon_refl kp hsb3'.common
      x19_eq := by cases sb3; exact hsb3'.x19_eq
      x22_eq := by rw [hr0_b3]; cases sb3; exact hsb3'.x22_eq
      x23_eq := by cases sb3; exact hsb3'.x23_eq
      x24_eq := by cases sb3; exact hsb3'.x24_eq
      x26_eq := by cases sb3; exact hsb3'.x26_eq
      x28_eq := by rw [hesp_b3]; cases sb3; exact hsb3'.x28_eq
      hmac_64 := by rw [hesp_b3]; exact (stripS_hmacStGen kp).mpr hsb3'.hmac_64
      okm_pre := by rw [hr0_b3, stripS_readBytes]; exact hsb3'.okm_pre }
  have hQ_c := iter_c_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H)
    hpre_b3_strip hrem hdst hsb3_strip
  refine (lift_block_vm_compress_only (C := C) (H := H) (i := 53) (j := 53)
    (Pj := (blkPC_53).rebase (blkPl_53).base H)
    blkLib_eq_53 blk53_noSvc0 blk53_noMsr (by decide) (by decide) hcl_b3
    (runsTo_53_to_bp hP_c) (runsTo_53_to_bp hQ_c)
    (fun _ h => h.common.status) (fun _ h => h.common.status)
    (fun sf hvm hq => unstrip_stateLoopC_96Placed hq hvm.perm_eq)).mono fun sc hsc => ?_
  exact
    { pc_eq := hsc.pc_eq, common := expandCommon_trans_frame hf_s_b3 hsc.common,
      lr_eq := hsc.lr_eq, x0_eq := hsc.x0_eq, x1_eq := hsc.x1_eq,
      x19_eq := hsc.x19_eq, x21_eq := hsc.x21_eq, x22_eq := hsc.x22_eq,
      x23_eq := hsc.x23_eq, x24_eq := hsc.x24_eq, x26_eq := hsc.x26_eq,
      x28_eq := hsc.x28_eq, hmac_240 := hsc.hmac_240, okm_pre := hsc.okm_pre }

private theorem run_done_ep_96_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀)
    (hf : ExpandFrameS2 96 s₀ s.mem)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 2 32 64
      (s₀.setMem s.mem) s) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand C.F prk info 96 ∧
      ExpandFrameS2 96 s₀ sf.mem := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hpre_s := hb.at_mem s.mem hf
  refine (iter_d_done_96_hmc (C := C) (H := H) hH.memcpy hpre_s hokm hx).trans_full
    fun sd hsd hkfd => ?_
  have hcl_d := hcl.of_keepsFrozen hkfd
  have hf_d : ExpandFrameS2 96 s₀ sd.mem := hf.trans (S2Frame.of_frame hsd.common.frame)
  have hpre_d := hb.at_mem sd.mem hf_d
  have hsd' : StateDone expPlacedFakeB C.F prk info 96 (s₀.setMem sd.mem) sd :=
    { pc_eq := hsd.pc_eq, common := expandCommon_setMem_self hsd.common, okm_all := hsd.okm_all }
  have hrunsP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) sd (fun sf =>
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand C.F prk info 96 ∧
      ExpandFrame 96 (s₀.setMem sd.mem) sf.mem) :=
    (epilogue_96_raw_hmc (C := C) (H := H) hpre_d hsd').mono
      fun sf ⟨hpc, hrun, hcs, hokm_f, hfr⟩ => ⟨hpc, hrun, ⟨hcs.1, hcs.2⟩, hokm_f, hfr⟩
  have hpre_d_strip := expandPre96_46_stripS hpre_d kp
  have hr0 : ∀ r, (ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 r = s₀.readReg64 r :=
    fun _ => by cases s₀; rfl
  have hsd_strip : StateDone expPlacedFakeB C.F prk info 96
      (ProofLib.stripS kp (s₀.setMem sd.mem)) (ProofLib.stripS kp sd) :=
    { pc_eq := by cases sd; exact hsd'.pc_eq
      common := stripS_expandCommon_refl kp hsd'.common
      okm_all := by rw [hr0, stripS_readBytes]; exact hsd'.okm_all }
  have hrunsQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
      (ProofLib.stripS kp sd) (fun sf' =>
        sf'.pc = (ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 .lr ∧
        sf'.status = .Running ∧
        CalleeSaved (ProofLib.stripS kp (s₀.setMem sd.mem)) sf' ∧
        sf'.mem.readBytes ((ProofLib.stripS kp (s₀.setMem sd.mem)).readReg64 .x2) 96 =
          hkdfExpand C.F prk info 96 ∧
        ExpandFrame 96 (ProofLib.stripS kp (s₀.setMem sd.mem)) sf'.mem) :=
    (epilogue_96_raw_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre_d_strip hsd_strip).mono
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

private theorem expand_multi_info_96_46_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : ExpandPre96_46Base C.F prk info infoPtr s₀) :
    RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes (s₀.readReg64 .x2) 96 = hkdfExpand C.F prk info 96 ∧
      ExpandFrameS2 96 s₀ sf.mem := by
  let Q53 := libsignalSessionLib.blockProgram lsmpl 53 (hmacCompressOnlyExcHooks C.F H)
  let kp := ProofLib.progKeep Q53
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : ExpandFrameS2 96 s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hpre₀ := hb.at_mem s₀.mem hf₀
  -- Piece 1a: `s₀ → StateX1Placed` (`seg0 ∘ seg1` in Block `53`)
  have h_run01 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX1Placed C.F prk info infoPtr 96 (s₀.setMem s₀.mem)) := by
    have hP : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
        (StateX1Placed C.F prk info infoPtr 96 (s₀.setMem s₀.mem)) := by
      conv => arg 2; rw [← hs_id]
      exact (seg0_96_hmc (C := C) (H := H) hpre₀).trans fun s1 hs1 =>
        seg1_96_hmc (C := C) (H := H) hpre₀ hs1
    have hpre₀_strip := expandPre96_46_stripS hpre₀ kp
    have hs_strip_id : ProofLib.stripS kp (s₀.setMem s₀.mem) = ProofLib.stripS kp s₀ := by
      rw [hs_id]
    have hQ : RunsTo ((blkPC_53).rebase (blkPl_53).base (hmacCompressOnlyExcHooks C.F H))
        (ProofLib.stripS kp s₀)
        (StateX1Placed C.F prk info infoPtr 96 (ProofLib.stripS kp (s₀.setMem s₀.mem))) := by
      conv => arg 2; rw [← hs_strip_id]
      exact (seg0_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre₀_strip).trans
        fun s1 hs1 => seg1_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre₀_strip hs1
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
  -- Piece 1b: `seg2a_96_hmc ∘ seg2b_96_hmc` (`StateX1Placed → StateX2Placed`)
  have h_run1 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (fun s4 => ∃ m0, ExpandFrameS2 96 s₀ m0 ∧
        StateX2Placed C.F prk info 96 (s₀.setMem m0) s4) :=
    h_run01.trans_full fun s2 hs2 hkf2 =>
      (seg2a_96_hmc (C := C) (H := H) hH.memcpy hpre₀ hb.read_info hs2).trans_full
        fun s3 hs3 hkf3 => by
          have hcl3 := (hcl₀.of_keepsFrozen hkf2).of_keepsFrozen hkf3
          have hf3 : ExpandFrameS2 96 s₀ s3.mem := hf₀.trans (S2Frame.of_frame hs3.common.frame)
          have hpre3 := hb.at_mem s3.mem hf3
          have hs3' : StateX1b expPlacedFakeB C.F prk info 96 (s₀.setMem s3.mem) s3 :=
            { pc_eq := hs3.pc_eq, common := expandCommon_setMem_self hs3.common,
              x22_eq := hs3.x22_eq, x23_eq := hs3.x23_eq,
              x26_eq := hs3.x26_eq, hmac_64 := hs3.hmac_64 }
          have hP := seg2b_96_hmc (C := C) (H := H) hpre3 hs3'
          have hpre3_strip := expandPre96_46_stripS hpre3 kp
          have hesp3 : esp (ProofLib.stripS kp (s₀.setMem s3.mem)) = esp s₀ := by
            rw [esp_stripS, esp_setMem]
          have hr03 : ∀ r, (ProofLib.stripS kp (s₀.setMem s3.mem)).readReg64 r = s₀.readReg64 r :=
            fun _ => by cases s₀; rfl
          have hs3_strip : StateX1b expPlacedFakeB C.F prk info 96
              (ProofLib.stripS kp (s₀.setMem s3.mem)) (ProofLib.stripS kp s3) :=
            { pc_eq := by cases s3; exact hs3'.pc_eq
              common := stripS_expandCommon_refl kp hs3'.common
              x22_eq := by rw [hr03]; cases s3; exact hs3'.x22_eq
              x23_eq := by cases s3; exact hs3'.x23_eq
              x26_eq := by cases s3; exact hs3'.x26_eq
              hmac_64 := by rw [hesp3]; exact (stripS_hmacSt kp).mpr hs3'.hmac_64 }
          have hQ := seg2b_96_hmc (C := C) (H := hmacCompressOnlyExcHooks C.F H) hpre3_strip hs3_strip
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
    fin1_96_placed_runsToVm_sat (C := C) (H := H) (hcl₀.of_keepsFrozen hkf4) hb hf0 hs4
  -- Piece 3: `seg3_96_hmc` (`s5 → StateLoop 1`) + `run_iter_to_loopC_96_vm` (`→ StateLoopC_96Placed 1`)
  have h_to_fin2 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (fun s6c => ∃ m1, ExpandFrameS2 96 s₀ m1 ∧
        StateLoopC_96Placed C.F prk info (t1 C.F prk info) (t1 C.F prk info)
          1 64 32 (s₀.setMem m1) s6c) :=
    h_after_fin1.trans_full fun s5 ⟨m1, hf1, hm1_eq, hs5⟩ hkf5 => by
      subst hm1_eq
      have hcl5 := hcl₀.of_keepsFrozen hkf5
      have hpre5 := hb.at_mem s5.mem hf1
      refine (seg3_96_hmc (C := C) (H := H) hH.memcpy hpre5 hs5).trans_full fun sl hsl hkfl => ?_
      have hf_sl : ExpandFrameS2 96 s₀ sl.mem := hf1.trans (S2Frame.of_frame hsl.common.frame)
      have hsl_re : StateLoop expPlacedFakeB 96 (t1 C.F prk info) (t1 C.F prk info)
          1 64 32 (s₀.setMem sl.mem) sl :=
        { pc_eq := hsl.pc_eq, common := expandCommon_setMem_self hsl.common,
          x19_eq := hsl.x19_eq, x22_eq := hsl.x22_eq, x24_eq := hsl.x24_eq,
          x26_eq := hsl.x26_eq, x28_eq := hsl.x28_eq,
          t_cache := hsl.t_cache, okm_pre := hsl.okm_pre }
      exact (run_iter_to_loopC_96_vm (C := C) (H := H)
        (hcl5.of_keepsFrozen hkfl) hb hf_sl (t1_length C.F prk info)
        (Or.inl rfl) (Or.inl rfl) (by decide) hsl_re).mono fun s6c hs6c => ⟨sl.mem, hf_sl, hs6c⟩
  -- Piece 4: `iter_fin` #1 (`finalize_fixed` #2 in Block `123`)
  have h_after_fin2 := h_to_fin2.trans_full fun s6c ⟨m1, hf1, hs6c⟩ hkf6 =>
    iter_fin_96_placed_runsToVm_sat (C := C) (H := H)
      (hcl₀.of_keepsFrozen hkf6) hb hf1 (t1_length C.F prk info) (Or.inl rfl) (by decide) hs6c
  -- Piece 5: `iter_d_continue_96_hmc` + `run_iter_to_loopC_96_vm` (`→ StateLoopC_96Placed 2`)
  have h_to_fin3 : RunsToVm ((blkPC_53).rebase (blkPl_53).base H) s₀
      (fun s8c => ∃ m2, ExpandFrameS2 96 s₀ m2 ∧
        StateLoopC_96Placed C.F prk info (t2 C.F prk info)
          (t1 C.F prk info ++ t2 C.F prk info) 2 32 64 (s₀.setMem m2) s8c) :=
    h_after_fin2.trans_full fun s7 ⟨m2, hf2, hm2_eq, hs7⟩ hkf7 => by
      subst hm2_eq
      have hcl7 := hcl₀.of_keepsFrozen hkf7
      have hpre7 := hb.at_mem s7.mem hf2
      refine (iter_d_continue_96_hmc (C := C) (H := H) hH.memcpy (tNext := t2 C.F prk info)
        hpre7 rfl hs7).trans_full fun sl hsl hkfl => ?_
      have hf_sl : ExpandFrameS2 96 s₀ sl.mem := hf2.trans (S2Frame.of_frame hsl.common.frame)
      have hsl_re : StateLoop expPlacedFakeB 96 (t2 C.F prk info)
          (t1 C.F prk info ++ t2 C.F prk info) 2 32 64 (s₀.setMem sl.mem) sl :=
        { pc_eq := hsl.pc_eq, common := expandCommon_setMem_self hsl.common,
          x19_eq := hsl.x19_eq, x22_eq := hsl.x22_eq, x24_eq := hsl.x24_eq,
          x26_eq := hsl.x26_eq, x28_eq := hsl.x28_eq,
          t_cache := hsl.t_cache, okm_pre := hsl.okm_pre }
      exact (run_iter_to_loopC_96_vm (C := C) (H := H)
        (hcl7.of_keepsFrozen hkfl) hb hf_sl (t2_length C.F prk info)
        (Or.inr rfl) (Or.inr rfl) (by decide) hsl_re).mono fun s8c hs8c => ⟨sl.mem, hf_sl, hs8c⟩
  -- Piece 6: `iter_fin` #2 (`finalize_fixed` #3 in Block `123`) + `run_done_ep_96_vm`
  refine h_to_fin3.trans_full fun s8c ⟨m2, hf2, hs8c⟩ hkf8 => ?_
  have hcl8 := hcl₀.of_keepsFrozen hkf8
  have hfin3 := iter_fin_96_placed_runsToVm_sat (C := C) (H := H) hcl8 hb hf2
    (t2_length C.F prk info) (Or.inr rfl) (by decide) hs8c
  refine hfin3.trans_full fun s9 ⟨m3, hf3, hm3_eq, hs9⟩ hkf9 => ?_
  subst hm3_eq
  have hokm96 : (t1 C.F prk info ++ t2 C.F prk info) ++
      hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) =
      hkdfExpand C.F prk info 96 := by
    rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
        hkdfExpand_96_eq]
  exact run_done_ep_96_vm (C := C) (H := H) (hcl8.of_keepsFrozen hkf9) hb hf3 hokm96 hs9

/-! ## 3. Top-Level `expand_multi_info_96_46_placed_vm_ok_sat` Contract -/

/-- `HookSat` + `HookSatExactMemcpy` sibling of
`CryptoCalleesPlacedBudgetAux.expand_multi_info_96_46_placed_vm_ok`:
relocatable `subroutine_ok` with `VmPreserved` for `expand_multi_info` (Block `53`) when
`okmLen = 96` and `info.length = 46` under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem expand_multi_info_96_46_placed_vm_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactBudgetSat C.F H] :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
      (withLsCodeLoaded lsmpl (withVmPreserved (expandMultiInfo96_46Spec C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [withVmPreserved, expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack,
    finalizeFixedStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA 96 ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) 46#64
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = 46#64) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA 96
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA 96 ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA 96 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA 96 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hrw_hm : s0.mem.RW x.hkdfA 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha
  have hrw_hdr : s0.mem.RW x.infoHdrA 16 := fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha
  have hrw_okm : s0.mem.RW x.okmA 96 := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (s0.sp - 640#64) 640 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have h_exp_pre0 : ExpandPre96_46 expPlacedFakeB C.F x.prk x.info x.infoA s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_len_eq := hinfo_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := by rw [← hinfo_len]; exact hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable hrw_hm
      read_x1 := by rw [hx1]; exact Memory.RW.readable hrw_hdr
      rw_x2 := by rw [hx2]; exact hrw_okm
      rw_stack := hrw_stk
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk (by decide) (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) (by decide) hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) (by decide) hsep_hdr_okm
      out_info_stk := by rw [← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by
        rw [hx2, ← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have hb_base : ExpandPre96_46Base C.F x.prk x.info x.infoA s0 :=
    { pre := h_exp_pre0
      read_info := fun a ha =>
        ⟨by rw [← hinfo_len] at ha; exact hro_info.perm_r hsep_info_stk ha,
         by rw [← hinfo_len] at ha; exact hro_info.isLazyFree_false hsep_info_stk ha⟩ }
  intro hL0
  obtain ⟨sf, hsteps, hvm, htr, hv, ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    expand_multi_info_96_46_placed_runsToVm_sat (C := C) (H := H) hcl hb_base hL0
  refine ⟨sf, hsteps, Or.inl ⟨hpc_sf, hstat_sf, ?_,
    CallingConventionPreserved_of_calleeSaved hcallee ⟨htr, hv⟩⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfo96_46Spec, stackAt,
    expandMultiInfoStack, finalizeFixedStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  unfold ExpandFrameS2 at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info 96).length = 96 := by
    rw [hkdfExpand_96_eq]
    simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; decide, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxCSat
