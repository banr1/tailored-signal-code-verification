/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePending
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Segment 3: `pending_pre_key` & `pending_kyber_pre_key`

Proves `clonePending_vregs_placed_ok` (`+0x1a5c → +0x1b20`, `genP3J2Placed → genP3J3Placed`)
on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Sub-Segment 3B: `pending_kyber_pre_key` (`+0x1ac8 → +0x1b20`) -/

set_option maxHeartbeats 400000 in
private theorem kyb_none_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      ((coroPtr + 0x220#64) ↦₆₄ noneCap)
      (fun s1 P_f =>
        (P_f ⊢ (coroPtr + 0x220#64) ↦₆₄ noneCap) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = noneCap ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [noneCap] at *
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem kyb_some_nil_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr cap v08 : BitVec 64) (kw0 v24 : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (((coroPtr + 0x220#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x230#64) ↦₆₄ 0#64) ∗
        ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x8#64) ↦₆₄ v08) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x230#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
            ((s.sp + 0x8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x24#64) ↦₃₂ kw0)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem kyb_some_pos_prep_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (s : State) (coroPtr cap srcPtr : BitVec 64) (len : Nat) (kw0 v24 : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpos : 0 < len)
    (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (((coroPtr + 0x220#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x228#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x230#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x220#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x228#64) ↦₆₄ srcPtr) ∗
            ((coroPtr + 0x230#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((coroPtr + 0x238#64) ↦₃₂ kw0) ∗
            ((s.sp + 0x24#64) ↦₃₂ kw0)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = srcPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1af8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim' := closure_shim_placed_ok ext hshim
  have hcmn : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcmn_beq : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
  have hlen_ne : BitVec.ofNat 64 len ≠ 0#64 := ofNat_ne_zero_of_pos hpos (Nat.lt_trans hlen_lt (by decide))
  have hlen_beq : (BitVec.ofNat 64 len == 0#64) = false := beq_ofNat_zero_eq_false hpos (Nat.lt_trans hlen_lt (by decide))
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hshim' ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem kyb_oom_cbz_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1af8#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x375c#64) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl⟩

set_option maxHeartbeats 400000 in
private theorem kyb_some_pos_copy_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s : State) (ptr' srcPtr v08 : BitVec 64) (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64)
    (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1af8#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx21 : s.readReg64 .x21 = srcPtr)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 bs.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (memRegion ptr' bs.length ∗
        (srcPtr ↦ₛ bs) ∗
        stackAt s.sp allocHookStack ∗
        ((s.sp + 0x8#64) ↦₆₄ v08))
      (fun s1 P_f =>
        (P_f ⊢
          (ptr' ↦ₛ bs) ∗
            (srcPtr ↦ₛ bs) ∗
            stackAt s.sp allocHookStack ∗
            ((s.sp + 0x8#64) ↦₆₄ ptr')) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = BitVec.ofNat 64 bs.length ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy' := closure_memcpy_4k_placed_ok ext hmemcpy
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have hlen_le64 : bs.length ≤ 2 ^ 64 := by omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only [withStack] at hmemcpy' ⊢
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx21' : s.readReg64 (Reg.gpr 21#5) = srcPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = BitVec.ofNat 64 bs.length := hx26
  wp_steps
  wp_call hmemcpy' (ptr', srcPtr, bs)
  clear hmemcpy'
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem clonePendingKyber_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr v08 : BitVec 64) (v24 : BitVec 32)
    (kyber : Option TailVecGhost) (F : SepProp)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1ac8#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (w24 : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1b20#64 → s1.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = kybCap' → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 32 (coroPtr + 0x220#64) kyber ∗
          OptKybClone A kyber kybCap' kybPtr' ∗ ((sp + 0x8#64) ↦₆₄ kybPtr') ∗
          ((sp + 0x24#64) ↦₃₂ w24) ∗ F)
        Q (P3P4.PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 32 (coroPtr + 0x220#64) kyber ∗
        ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗ F)
      Q (P3P4.PanicOomProp s0) := by
  cases kyber with
  | none =>
    dsimp only [optTailVecAt, OptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    have hnone := kyb_none_placed_wp ext s coroPtr hpc hrun hx19
    refine bind_sepWP_lscro_frame_placed hcro hnone (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1,
      hx26_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
    have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
    have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
    have h_rfl : (⌜noneCap = noneCap⌝ : SepProp) = emp := segClone_pure_eq_emp rfl
    refine SepWPp.weaken_pre ?_
      (hnext s1 noneCap v08 v24 hpc1 hrun1 hcro1 hsp1 hsp1_al
        (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1)
    rw [h_rfl]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | some gk =>
    dsimp only [optTailVecAt, OptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine pure_elim_3 fun htail => ?_
    obtain ⟨kw0, kw1, _, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h228 : coroPtr + 0x220#64 + 8#64 = coroPtr + 0x228#64 := by bv_arith
    have h230 : coroPtr + 0x220#64 + 16#64 = coroPtr + 0x230#64 := by bv_arith
    have h238 : coroPtr + 0x220#64 + BitVec.ofNat 64 24 = coroPtr + 0x238#64 := by bv_arith
    have h23c : coroPtr + 0x238#64 + 4#64 = coroPtr + 0x23c#64 := by bv_arith
    rw [h238, htail_pts (coroPtr + 0x238#64), h23c]
    rcases list_eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gk.vec (coroPtr + 0x220#64) hnil, h228, h230]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hcap_lt, hptr⟩ => ?_
      rw [← hsp_eq]
      have hnil_wp := kyb_some_nil_placed_wp ext s coroPtr gk.vec.cap v08 kw0 v24
        hcap_lt hpc hrun hsp_al hx19
      refine bind_sepWP_lscro_frame_placed hcro hnil_wp (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
      rw [hsp_eq]
      have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s1 0#64 1#64 kw0 hpc1 hrun1 hcro1 hsp1 hsp1_al
          (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs1)
      rw [vecGhostAt_eq_of_nil A gk.vec (coroPtr + 0x220#64) hnil, h228, h230,
          h238, htail_pts (coroPtr + 0x238#64), h23c,
          hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gk.vec (coroPtr + 0x220#64) hpos, h228, h230]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk gk.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
      have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← hsp_eq]
      have hprep := kyb_some_pos_prep_placed_wp ext hshim s coroPtr gk.vec.cap gk.vec.ptr
        gk.vec.bytes.length kw0 v24 hcap_lt hpos hlen_lt hpc hrun hsp_al hx19
      refine bind_sepWP_lscro_frame_placed hcro hprep (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1,
        hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
      rw [hsp_eq]
      have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
      have htr1 : s1.trace = s0.trace := htr1_s.trans htr
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hφ : (s1.readReg64 .x0).toNat = gk.vec.bytes.length ∧
          (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk gk.vec.bytes.length 1 :=
        ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hlay⟩
      refine call_raw_nopanic_placed
        (spec := rustAllocSpec A)
        (x := (gk.vec.bytes.length, 1))
        (T := A.pool ∗ stackAt sp allocHookStack)
        hcro1 halloc hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [rustAllocSpec]; rw [hsp1])
        hφ (by sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, _, hx25_cs2,
        hx26_cs2, hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
      have hx21_2 : s2.readReg64 .x21 = gk.vec.ptr := hx21_cs2.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hx22_cs2.trans hx22_1
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hx23_cs2.trans hx23_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
      have hx26_2 : s2.readReg64 .x26 = BitVec.ofNat 64 gk.vec.bytes.length := hx26_cs2.trans hx26_1
      have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hx27_cs2.trans hx27_1
      have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hx28_cs2.trans hx28_1
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
      dsimp only [rustAllocSpec]
      rw [hsp1]
      by_cases hoom : s2.readReg64 .x0 = 0#64
      · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
        simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
        refine SepWPp.pure_elim fun htr2_1 => ?_
        have hcbz := kyb_oom_cbz_placed_wp ext s2 hpc2 hrun2 hoom
        refine bind_sepWP_lscro_frame_placed hcro2 hcbz (emp_sepConj _).symm
          fun s3 hpc3 hrun3 hcro3 ⟨_, htr3_2⟩ => ?_
        exact oom_tail_375c_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3
          (by rw [htr3_2, htr2_1, htr1])
      · set ptr' := s2.readReg64 .x0
        have hoom0 : (ptr' = 0) = False := eq_false hoom
        simp only [hoom0, ↓reduceIte, sepConj_assoc]
        refine pure_elim_3 fun ⟨_, htr2_1⟩ => ?_
        have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
        rw [← hsp2]
        have hcopy := kyb_some_pos_copy_placed_wp ext hmemcpy s2 ptr' gk.vec.ptr
          v08 gk.vec.bytes hoom hlen_lt hpc2 hrun2 hsp2_al rfl hx21_2 hx26_2
        refine bind_sepWP_lscro_frame_placed hcro2 hcopy (by sep_focus)
          fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
        rcases hregs3 with ⟨hsp3_2, htr3_2, hx19_3, hx22_3, hx23_3, hx25_3,
          hx26_3, hx27_3, hx28_3, hx29_3, hvregs3_2⟩
        rw [hsp2]
        refine P3P4.SepWPp.weaken_frame
          (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
        have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
        have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp2_al
        have h_rfl : (⌜BitVec.ofNat 64 gk.vec.bytes.length = BitVec.ofNat 64 gk.vec.bytes.length⌝ : SepProp) = emp :=
          segClone_pure_eq_emp rfl
        have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
        have h_pure2 : (⌜gk.vec.bytes.length ≤ gk.vec.cap.toNat ∧ gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
          segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
        refine SepWPp.weaken_pre ?_
          (hnext s3 (BitVec.ofNat 64 gk.vec.bytes.length) ptr' kw0
            hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
            (hx19_3.trans hx19_2) (hx22_3.trans hx22_2) (hx23_3.trans hx23_2)
            (hx25_3.trans hx25_2) hx26_3 (hx27_3.trans hx27_2)
            (hx28_3.trans hx28_2) (hx29_3.trans hx29_2)
            (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
        rw [vecGhostAt_eq_of_pos A gk.vec (coroPtr + 0x220#64) hpos, h228, h230,
            h238, htail_pts (coroPtr + 0x238#64), h23c,
            vecU8Buf_pos_eq A ptr' gk.vec.bytes hpos hlen_lt hoom,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option maxHeartbeats 800000 in
/-- Placed Segment 3 with `calleeSavedVRegs` (`+0x1a5c → +0x1b20`, `genP3J2Placed → genP3J3Placed`). -/
theorem clonePending_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (_hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1b20#64) s
      (genP3J2Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J3Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
          rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  dsimp only [genP3J2Placed, genP3PendSpillScratch]
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_elim
    fun ⟨hsp, hx19, hx23, hx25, _hx27, hx28, hx29, hch_len, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_coro_pending_eq A coroPtr recG st]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ps => ?_
  refine SepWPp.pure_elim fun hpure => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 48 (coroPtr + 0x1f0#64) recG.pending ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ ps.v10) ∗ ((sp + 0x18#64) ↦₆₄ ps.v18) ∗
            ((sp + 0x28#64) ↦₃₂ ps.v28) ∗ ((sp + 0x2c#64) ↦₃₂ ps.v2c) ∗
            (optTailVecAt A 32 (coroPtr + 0x220#64) recG.kyber ∗
              ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
              m3a3SessionStateRestAt A coroPtr recG st ∗ memRegion (sp + 0x3e0#64) 104 ∗
              genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
              vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
              vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
              optSenderChainHeap A w.sender' st.senderChain ∗
              vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
                (w.chains'.zip st.receiverChains) ∗
              genP3TailSpillScratch sp ∗ ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
              ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
              ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
              ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
              ((sp + 0x98#64) ↦₆₄ 32#64) ∗ ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
              genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
    (Entails.of_eq (by ac_rfl)) ?_
  refine clonePendingPreKey_placed_ok ext hpanic hshim halloc hmemcpy s0 s _ _ sp coroPtr ctxPtr
    ps.v10 ps.v18 ps.v28 ps.v2c recG.pending _ hcro hpc hrun hsp hsp_al htr hx19
    fun s1 pendCap' pendPtr' d10 w28 w2c hpc1 hrun1 hcro1 hsp1 hsp1_al htr1
      hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1 => ?_
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 32 (coroPtr + 0x220#64) recG.kyber ∗
            ((sp + 0x8#64) ↦₆₄ ps.v08) ∗ ((sp + 0x24#64) ↦₃₂ ps.v24) ∗
            (optTailVecAt A 48 (coroPtr + 0x1f0#64) recG.pending ∗
              OptPendClone A recG.pending pendCap' pendPtr' ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗
              m3a3SessionStateRestAt A coroPtr recG st ∗ memRegion (sp + 0x3e0#64) 104 ∗
              genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg ∗
              vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr recG.remoteIk.bytes ∗
              vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
              optSenderChainHeap A w.sender' st.senderChain ∗
              vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 st.receiverChains.length) w.newRcPtr
                (w.chains'.zip st.receiverChains) ∗
              genP3TailSpillScratch sp ∗ ((sp + 0x48#64) ↦₆₄ w.c0) ∗ ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
              ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗ ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
              ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
              ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗ ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
              ((sp + 0x98#64) ↦₆₄ 32#64) ∗ ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
              genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
    (Entails.of_eq (by ac_rfl)) ?_
  refine clonePendingKyber_placed_ok ext hpanic hshim halloc hmemcpy s0 s1 _ _ sp coroPtr ps.v08 ps.v24
    recG.kyber _ hcro1 hpc1 hrun1 hsp1 hsp1_al htr1 hx19_1
    fun sf kybCap' kybPtr' w24 hpcf hrunf hcrof hspf _hspf_al htrf
      hx19_f hx22_f hx23_f hx25_f hx26_f hx27_f hx28_f hx29_f hvregsf => ?_
  refine sepWPp_done hpcf hrunf ⟨?_, htrf, hcrof, hvregsf.trans hvregs1⟩
  let w' : GenP3J3Witness :=
    { toGenP3J2Witness := w, pendCap' := pendCap', pendPtr' := pendPtr',
      kybCap' := kybCap', kybPtr' := kybPtr', d10 := d10, w24 := w24, w28 := w28, w2c := w2c }
  refine Entails.sepExists_right w' ?_
  apply Entails.pure_right
    ⟨hspf, hx19_f, hx22_f.trans hx22_1, hx23_f.trans (hx23_1.trans hx23),
     hx25_f.trans (hx25_1.trans hx25), hx26_f, hx27_f.trans hx27_1,
     hx28_f.trans (hx28_1.trans hx28), hx29_f.trans (hx29_1.trans hx29),
     hch_len, hsc_rel, hsc_inl⟩
  dsimp only [genP3J3Placed, w']
  rw [sessionStateAt_coro_pending_eq A coroPtr recG st]
  simp only [sepConj_assoc]
  apply Entails.pure_right hpure
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
