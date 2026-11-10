/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingSteps
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Sub-Segment 3A: `pending_pre_key`

Relocatable `[LibsignalPlacement]` OOM tail (`+0x378c`) and CPS sub-segment theorem
`clonePendingPreKey_placed_ok` (`+0x1a5c → +0x1ac8`) on `lsProg_518 ext`.
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

/-! ## 1. OOM Exit Tail (`+0x378c..+0x3794`) -/

set_option maxHeartbeats 400000 in
theorem oom_tail_378c_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x378c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hp := closure_panic_at_handle_error_placed ext hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_lscro_frame_placed hcro hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hp) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/-! ## 2. Sub-Segment 3A: `pending_pre_key` (`+0x1a5c → +0x1ac8`) -/

set_option maxHeartbeats 400000 in
private theorem pend_none_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (((coroPtr + 0x1f0#64) ↦₆₄ noneCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x1f0#64) ↦₆₄ noneCap) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = noneCap ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧
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
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem pend_some_nil_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr cap td2 v10 v18 : BitVec 64)
    (tw0 tw1 tw3 v28 v2c : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗ ((coroPtr + 0x200#64) ↦₆₄ 0#64) ∗
        ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗ ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
        ((coroPtr + 0x210#64) ↦₆₄ td2) ∗ ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0x10#64) ↦₆₄ v10) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗ ((coroPtr + 0x200#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗ ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
            ((coroPtr + 0x210#64) ↦₆₄ td2) ∗ ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((s.sp + 0x10#64) ↦₆₄ td2) ∗
            ((s.sp + 0x18#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x28#64) ↦₃₂ tw3) ∗ ((s.sp + 0x2c#64) ↦₃₂ tw0)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
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
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem pend_some_pos_prep_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (s : State) (coroPtr ctxPtr cap srcPtr : BitVec 64) (len : Nat)
    (tw0 tw1 tw3 v28 v2c : BitVec 32)
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpos : 0 < len)
    (hlen_lt : len < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      (((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗
        ((coroPtr + 0x1f8#64) ↦₆₄ srcPtr) ∗
        ((coroPtr + 0x200#64) ↦₆₄ BitVec.ofNat 64 len) ∗
        ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗
        ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
        ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
        ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x1f0#64) ↦₆₄ cap) ∗
            ((coroPtr + 0x1f8#64) ↦₆₄ srcPtr) ∗
            ((coroPtr + 0x200#64) ↦₆₄ BitVec.ofNat 64 len) ∗
            ((coroPtr + 0x208#64) ↦₃₂ tw0) ∗
            ((coroPtr + 0x20c#64) ↦₃₂ tw1) ∗
            ((coroPtr + 0x218#64) ↦₃₂ tw3) ∗
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x28#64) ↦₃₂ tw3) ∗
            ((s.sp + 0x2c#64) ↦₃₂ tw0)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x1 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = srcPtr ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1a98#64 ∧
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
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem pend_oom_cbz_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1a98#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x378c#64) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl⟩

set_option maxHeartbeats 400000 in
private theorem pend_some_pos_copy_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s : State) (coroPtr ptr' srcPtr td2 v10 v18 : BitVec 64)
    (bs : List (BitVec 8))
    (hptr : ptr' ≠ 0#64)
    (hlen_lt : bs.length < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a98#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = srcPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 bs.length) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ac8#64) s
      (memRegion ptr' bs.length ∗
        (srcPtr ↦ₛ bs) ∗
        stackAt s.sp allocHookStack ∗
        ((coroPtr + 0x210#64) ↦₆₄ td2) ∗
        ((s.sp + 0x10#64) ↦₆₄ v10) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18))
      (fun s1 P_f =>
        (P_f ⊢
          (ptr' ↦ₛ bs) ∗
            (srcPtr ↦ₛ bs) ∗
            stackAt s.sp allocHookStack ∗
            ((coroPtr + 0x210#64) ↦₆₄ td2) ∗
            ((s.sp + 0x10#64) ↦₆₄ td2) ∗
            ((s.sp + 0x18#64) ↦₆₄ ptr')) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = BitVec.ofNat 64 bs.length ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
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
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = srcPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 bs.length := hx22
  wp_steps
  wp_call hmemcpy' (ptr', srcPtr, bs)
  clear hmemcpy'
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem clonePendingPreKey_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr v10 v18 : BitVec 64)
    (v28 v2c : BitVec 32)
    (pending : Option TailVecGhost) (F : SepProp)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x1a5c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_al : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' d10 : BitVec 64) (w28 w2c : BitVec 32),
      s1.pc = (blkPl_518).base + 0x1ac8#64 → s1.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = sp → s1.spAligned = true → s1.trace = s0.trace →
      s1.readReg64 .x19 = coroPtr → s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x27 = ctxPtr → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 48 (coroPtr + 0x1f0#64) pending ∗
          OptPendClone A pending pendCap' pendPtr' ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0x10#64) ↦₆₄ d10) ∗ ((sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((sp + 0x28#64) ↦₃₂ w28) ∗ ((sp + 0x2c#64) ↦₃₂ w2c) ∗ F)
        Q (P3P4.PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool ∗ stackAt sp chainCloneStack ∗ optTailVecAt A 48 (coroPtr + 0x1f0#64) pending ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
        ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗ F)
      Q (P3P4.PanicOomProp s0) := by
  cases pending with
  | none =>
    dsimp only [optTailVecAt, OptPendClone] at hnext ⊢
    rw [← hsp_eq]
    simp only [sepConj_assoc]
    have hnone := pend_none_placed_wp ext s coroPtr ctxPtr hpc hrun hsp_al hx19
    refine bind_sepWP_lscro_frame_placed hcro hnone (by sep_focus)
      fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
    rw [hsp_eq]
    have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
    have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
    have h_rfl : (⌜noneCap = noneCap⌝ : SepProp) = emp := segClone_pure_eq_emp rfl
    refine SepWPp.weaken_pre ?_
      (hnext s1 noneCap v18 v10 v28 v2c hpc1 hrun1 hcro1 hsp1 hsp1_al
        (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1)
    rw [h_rfl]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | some gp =>
    dsimp only [optTailVecAt, OptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine pure_elim_3 fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, _, htail_pts⟩ := exists_tail24_decomp htail
    have h1f8 : coroPtr + 0x1f0#64 + 8#64 = coroPtr + 0x1f8#64 := by bv_arith
    have h200 : coroPtr + 0x1f0#64 + 16#64 = coroPtr + 0x200#64 := by bv_arith
    have h208 : coroPtr + 0x1f0#64 + BitVec.ofNat 64 24 = coroPtr + 0x208#64 := by bv_arith
    have h20c : coroPtr + 0x208#64 + 4#64 = coroPtr + 0x20c#64 := by bv_arith
    have h210 : coroPtr + 0x208#64 + 8#64 = coroPtr + 0x210#64 := by bv_arith
    have h218 : coroPtr + 0x208#64 + 16#64 = coroPtr + 0x218#64 := by bv_arith
    have h21c : coroPtr + 0x208#64 + 20#64 = coroPtr + 0x21c#64 := by bv_arith
    rw [h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c]
    rcases list_eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gp.vec (coroPtr + 0x1f0#64) hnil, h1f8, h200]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hcap_lt, hptr⟩ => ?_
      rw [← hsp_eq]
      have hnil_wp := pend_some_nil_placed_wp ext s coroPtr ctxPtr gp.vec.cap td2 v10 v18
        tw0 tw1 tw3 v28 v2c hcap_lt hpc hrun hsp_al hx19
      refine bind_sepWP_lscro_frame_placed hcro hnil_wp (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx22_1, hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
      rw [hsp_eq]
      have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      refine SepWPp.weaken_pre ?_
        (hnext s1 0#64 1#64 td2 tw3 tw0 hpc1 hrun1 hcro1 hsp1 hsp1_al
          (htr1_s.trans htr) hx19_1 hx22_1 hx23_1 hx25_1 hx27_1 hx28_1 hx29_1 hvregs1)
      rw [vecGhostAt_eq_of_nil A gp.vec (coroPtr + 0x1f0#64) hnil, h1f8, h200,
          h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c,
          hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gp.vec (coroPtr + 0x1f0#64) hpos, h1f8, h200]
      simp only [sepConj_assoc]
      refine pure_elim_3 fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
      have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
      have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← hsp_eq]
      have hprep := pend_some_pos_prep_placed_wp ext hshim s coroPtr ctxPtr gp.vec.cap gp.vec.ptr
        gp.vec.bytes.length tw0 tw1 tw3 v28 v2c hcap_lt hpos hlen_lt hpc hrun hsp_al hx19
      refine bind_sepWP_lscro_frame_placed hcro hprep (by sep_focus)
        fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
      rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx21_1, hx22_1,
        hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1_s⟩
      rw [hsp_eq]
      have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
      have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
      have htr1 : s1.trace = s0.trace := htr1_s.trans htr
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hφ : (s1.readReg64 .x0).toNat = gp.vec.bytes.length ∧
          (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk gp.vec.bytes.length 1 :=
        ⟨by rw [hx0_1, htoNat], by rw [hx1_1]; rfl, hlay⟩
      refine call_raw_nopanic_placed
        (spec := rustAllocSpec A)
        (x := (gp.vec.bytes.length, 1))
        (T := A.pool ∗ stackAt sp allocHookStack)
        hcro1 halloc hpc1 hrun1 hsp1_al hx30_1
        (by dsimp only [rustAllocSpec]; rw [hsp1])
        hφ (by sep_focus)
        (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, _, hx25_cs2, _,
        hx27_cs2, hx28_cs2, hx29_cs2, hvregs2_1⟩
      have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
      have hx21_2 : s2.readReg64 .x21 = gp.vec.ptr := hx21_cs2.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 gp.vec.bytes.length := hx22_cs2.trans hx22_1
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hx23_cs2.trans hx23_1
      have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
      have hx27_2 : s2.readReg64 .x27 = ctxPtr := hx27_cs2.trans hx27_1
      have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hx28_cs2.trans hx28_1
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hx29_cs2.trans hx29_1
      dsimp only [rustAllocSpec]
      rw [hsp1]
      by_cases hoom : s2.readReg64 .x0 = 0#64
      · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
        simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
        refine SepWPp.pure_elim fun htr2_1 => ?_
        have hcbz := pend_oom_cbz_placed_wp ext s2 hpc2 hrun2 hoom
        refine bind_sepWP_lscro_frame_placed hcro2 hcbz (emp_sepConj _).symm
          fun s3 hpc3 hrun3 hcro3 ⟨_, htr3_2⟩ => ?_
        exact oom_tail_378c_placed_ok ext hpanic s0 s3 _ _ _ hcro3 hpc3 hrun3
          (by rw [htr3_2, htr2_1, htr1])
      · set ptr' := s2.readReg64 .x0
        have hoom0 : (ptr' = 0) = False := eq_false hoom
        simp only [hoom0, ↓reduceIte, sepConj_assoc]
        refine pure_elim_3 fun ⟨_, htr2_1⟩ => ?_
        have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
        rw [← hsp2]
        have hcopy := pend_some_pos_copy_placed_wp ext hmemcpy s2 coroPtr ptr' gp.vec.ptr
          td2 v10 v18 gp.vec.bytes hoom hlen_lt hpc2 hrun2 hsp2_al rfl hx19_2 hx21_2 hx22_2
        refine bind_sepWP_lscro_frame_placed hcro2 hcopy (by sep_focus)
          fun s3 hpc3 hrun3 hcro3 hregs3 => ?_
        rcases hregs3 with ⟨hsp3_2, htr3_2, hx19_3, hx22_3, hx23_3, hx25_3, hx27_3, hx28_3, hx29_3, hvregs3_2⟩
        rw [hsp2]
        refine P3P4.SepWPp.weaken_frame
          (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
        have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
        have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp2_al
        have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length⌝ : SepProp) = emp :=
          segClone_pure_eq_emp rfl
        have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp := segClone_pure_eq_emp htail
        have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
          segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
        refine SepWPp.weaken_pre ?_
          (hnext s3 (BitVec.ofNat 64 gp.vec.bytes.length) ptr' td2 tw3 tw0
            hpc3 hrun3 hcro3 hsp3 hsp3_al (htr3_2.trans htr2)
            hx19_3 hx22_3 (hx23_3.trans hx23_2) (hx25_3.trans hx25_2)
            (hx27_3.trans hx27_2) (hx28_3.trans hx28_2) (hx29_3.trans hx29_2)
            (hvregs3_2.trans (hvregs2_1.trans hvregs1_s)))
        rw [vecGhostAt_eq_of_pos A gp.vec (coroPtr + 0x1f0#64) hpos, h1f8, h200,
            h208, htail_pts (coroPtr + 0x208#64), h20c, h210, h218, h21c,
            vecU8Buf_pos_eq A ptr' gp.vec.bytes hpos hlen_lt hoom,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a3
