/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecClone
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed `<Vec<Vec<u8>> as Clone>::clone` on 1 Element

Proves `VecVecClone1PlacedOkStmt A H` (`vecVecClone1_placed_okX_of_ser`) from `SerContractsXPlaced A H`
at `lsmpl.base 117` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record.Serialization CryptoVerification.E2E.Record.Placed
open Proofs.libsignal Proofs.libsignal.Hooks2 Proofs.libsignal.Stage1X

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓] VvcStateSimp.sp_setPC_pre
  VvcStateSimp.sp_setMem_setPC_pre VvcStateSimp.readReg64_setPC_pre
  VvcStateSimp.readReg64_setMem_setPC_pre VvcStateSimp.readReg32_setPC_pre
  VvcStateSimp.readReg32_setMem_setPC_pre
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_writeReg
  calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite calleeSavedVRegs_writeVReg32_ite
  isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Allocation-Error Panic Tails (`+0xec`, `+0xf8`) -/

private theorem sepWPp_of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP (sepWP_mono_lscl hcl h fun _ _ _ _ hclm hnext => hnext hclm)

set_option maxRecDepth 500000 in
theorem vvc1_panic_236_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {Q : State → SepProp → Prop} (x : VecVecClone1Ghost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_117).base + bv% (236))
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H)
      (s0.readReg64 (Reg.gpr 30#5)) s P Q (vvc1Qp A x s0 R) := by
  intro _
  have hpanic := hC.alloc.externAt_handle_error (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  change s.pc = (blkPl_117).base + 236#64 at hpc
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm, arm64_norm]; exact hpanic) fun hm => ?_
  simpa only [vecVecClone1SpecX, allocPanic, sepConj_assoc] using
    allowPanic_panicked (vvc1_allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

set_option maxRecDepth 500000 in
theorem vvc1_panic_248_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {Q : State → SepProp → Prop} (x : VecVecClone1Ghost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (blkPl_117).base + bv% (248))
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H)
      (s0.readReg64 (Reg.gpr 30#5)) s P Q (vvc1Qp A x s0 R) := by
  intro _
  have hpanic := hC.alloc.externAt_handle_error (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  change s.pc = (blkPl_117).base + 248#64 at hpc
  apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm, arm64_norm]; exact hpanic) fun hm => ?_
  simpa only [vecVecClone1SpecX, allocPanic, sepConj_assoc] using
    allowPanic_panicked (vvc1_allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## Epilogue (`+0xc8`) -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_epilogue_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64) (F : SepProp)
    (hent : vecHeader x.dst 1#64 q 1#64 ∗ F ⊢
      arrayAt (prevElem A) 24 x.src [x.enc] ∗ (∃∗ q' : BitVec 64, prevVecAt A x.dst 1#64 q' [x.enc]) ∗ A.pool)
    (hpc : s.pc = (blkPl_117).base + bv% (200)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_align : s.spAligned = true) (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst) (hx23 : s.readReg64 (Reg.gpr 23#5) = q)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ F)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro _
  change s.pc = (blkPl_117).base + 200#64 at hpc
  rw [vvc1_mem24_cells x.dst]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 => SepWPp.exists_elim fun d2 => ?_
  unfold vvc1Saved; simp only [sepConj_assoc]
  apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
  wp_steps; apply SepWP.done (by simp_all) (by simp_all); apply SepWPp.done (by simp_all) (by simp_all)
  refine ⟨?_, by simp_all, ?_⟩
  · intro hm
    simp only [vecVecClone1SpecX, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by simp_all, Satisfies.mono ?_ hm⟩
    rw [vvc1_stack_split]
    refine Entails.trans (Entails.of_eq (show _ = ((vecHeader x.dst 1#64 q 1#64 ∗ F) ∗
      (vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack) ∗ R) by
        unfold vecHeader vvc1Saved; ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left hent) ?_
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (vvc1_saved_cells s0)))) ?_
    exact Entails.of_eq (by ac_rfl)
  · constructor <;> simp_all

theorem vvc1_finish_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64) (hq : q ≠ 0#64)
    (hpc : s.pc = (blkPl_117).base + bv% (200)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_align : s.spAligned = true) (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst) (hx23 : s.readReg64 (Reg.gpr 23#5) = q)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗
        arrayAt (prevElem A) 24 x.src [x.enc] ∗ A.pool ∗ A.live q 24 8 ∗ vecU8 A q x.enc)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) :=
  vvc1_epilogue_placed x s0 s R q _ (vvc1_post_fold A x.src x.dst q x.enc hq) hpc hrun hsp hsp_align hx19 hx20
    hx23 htrace hvregs

/-! ## Post-Outer-Allocation Branches -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
/-- Placed empty-element branch (`L = 0`): writes `{0, 1, 0}` at `q`. -/
theorem vvc1_nil_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q cap ptr : BitVec 64) (SRC : SepProp)
    (henc : x.enc = []) (hq : q ≠ 0#64) (hs0_align : s0.spAligned = true)
    (hsrc : vecHeader x.src cap ptr 0#64 ∗ SRC ⊢ arrayAt (prevElem A) 24 x.src [x.enc])
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr 0#64 ∗ SRC ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗ A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hcl
  have hfin := fun s' => vvc1_finish_placed (A := A) (H := H) x s0 s' R q hq
  change s.pc = (blkPl_117).base + 68#64 at hpc
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96 hs0_align (by decide)
  rw [vvc1_mem24_cells q]; unfold vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_117).base + bv% (200))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_ep
  refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_ep)
  · have hel : (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A q x.enc := by
      rw [henc]; exact vvc1_elem_nil A q
    have hsrc' : (x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗ ((x.src + 16#64) ↦₆₄ 0#64) ∗ SRC ⊢
        arrayAt (prevElem A) 24 x.src [x.enc] := by
      refine Entails.trans ?_ hsrc; unfold vecHeader; exact Entails.of_eq (by simp only [sepConj_assoc])
    refine Entails.trans (Entails.of_eq (show _ = (((x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗
        ((x.src + 16#64) ↦₆₄ 0#64) ∗ SRC) ∗ ((q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64)) ∗
        (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ A.pool ∗
          A.live q 24 8)) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hsrc' (sepConj_mono_left hel)) ?_
    exact Entails.of_eq (by ac_rfl)
  all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]
  all_goals exact hs0_align

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
/-- Placed non-empty element branch (`L > 0`): allocates `p'`, copies `ptr` into `p'`, and writes
`{L, p', L}` at `q`. -/
theorem vvc1_cons_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp)
    (q cap ptr : BitVec 64) (SRCM : SepProp)
    (hpos : 0 < x.enc.length) (hlt : x.enc.length < 2 ^ 63) (hq : q ≠ 0#64) (hs0_align : s0.spAligned = true)
    (hsrc : vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ⊢
      arrayAt (prevElem A) 24 x.src [x.enc])
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ∗
        memRegion x.dst 24 ∗ A.pool ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗
        A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hcl
  have hshim := hC.alloc.shim (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  have halloc := hC.alloc.alloc (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  have hmemcpy := hC.memcpy (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  have hpanic236 := fun s' P => vvc1_panic_236_placed (A := A) (H := H) hC (Q := vvc1Q A x s0 R) x s0 s' P R
  have hfin := fun s' => vvc1_finish_placed (A := A) (H := H) x s0 s' R q hq
  change s.pc = (blkPl_117).base + 68#64 at hpc
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96 hs0_align (by decide)
  have hL : (BitVec.ofNat 64 x.enc.length).toNat = x.enc.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hLne : BitVec.ofNat 64 x.enc.length ≠ 0#64 := by
    intro h
    have h2 := congrArg BitVec.toNat h
    have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
    rw [hL, h0] at h2; omega
  have hLbeq : (BitVec.ofNat 64 x.enc.length == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; exact hLne
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayL : LayoutOk x.enc.length 1 := ⟨hpos, hpow1, by omega⟩
  rw [vvc1_mem24_cells q]; unfold vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_117).base + bv% (132))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_117).base + bv% (136))
  wp_steps; wp_call hshim_state (); apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_117).base + bv% (148))
  wp_steps; wp_call halloc_state (x.enc.length, 1)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_117).base + bv% (236))
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_panic
    refine hpanic236 _ _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_ hcl_panic
    simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace1⟩ => ?_
    have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_post_alloc
    apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_117).base + bv% (200))
    wp_steps; wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), ptr, x.enc)
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_ep
    refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcl_ep)
    · have hst : stackAt (s0.sp - 96#64) CryptoVerification.LibsignalTripleRatchet.extHookStack = stackAt (s0.sp - 96#64) Stage1X.extHookStack := rfl
      rw [show sf_1.sp = s0.sp - 96#64 by simp only [wp_norm, arm64_norm, *], hst]
      have hel := vvc1_elem_cons A q (sf_1.readReg64 (Reg.gpr 0#5)) x.enc hoom64 hpos hlt
      have hsrc' : (x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ⊢
          arrayAt (prevElem A) 24 x.src [x.enc] := by
        refine Entails.trans ?_ hsrc; unfold vecHeader; exact Entails.of_eq (by simp only [sepConj_assoc])
      refine Entails.trans (Entails.of_eq (show _ = (((x.src ↦₆₄ cap) ∗ ((x.src + 8#64) ↦₆₄ ptr) ∗
          ((x.src + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM) ∗
          ((q ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗ ((q + 8#64) ↦₆₄ sf_1.readReg64 (Reg.gpr 0#5)) ∗
            ((q + 16#64) ↦₆₄ BitVec.ofNat 64 x.enc.length) ∗
            A.live (sf_1.readReg64 (Reg.gpr 0#5)) x.enc.length 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ x.enc)) ∗
          (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ A.pool ∗
            A.live q 24 8)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hsrc' (sepConj_mono_left hel)) ?_
      exact Entails.of_eq (by ac_rfl)
    all_goals simp only [State.spAligned, wp_norm, arm64_norm, *]
    all_goals exact hs0_align

set_option maxRecDepth 500000 in
theorem vvc1_after_alloc_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64)
    (hs0_align : s0.spAligned = true) (hq : q ≠ 0#64)
    (hpc : s.pc = (blkPl_117).base + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗ A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hcl
  rw [vvc1_src_eq]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.pure_elim fun ⟨hlen, hcap63, hptr⟩ => ?_
  by_cases henc : x.enc = []
  · have hL : BitVec.ofNat 64 x.enc.length = 0#64 := by rw [henc]; rfl
    rw [hL]
    refine vvc1_nil_placed x s0 s R q cap ptr _ henc hq hs0_align ?_ hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace
      hvregs hcl
    have h := vvc1_src_fold A x.src cap ptr x.enc ⟨hlen, hcap63, hptr⟩
    rw [hL] at h; exact h
  · have hpos : 0 < x.enc.length := List.length_pos_iff.mpr henc
    have hcap : ¬ (cap = 0) := by
      intro h; subst h
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at hlen; omega
    have hfold := vvc1_src_fold A x.src cap ptr x.enc ⟨hlen, hcap63, hptr⟩
    simp only [hcap, ↓reduceIte] at hfold
    simp only [hcap, ↓reduceIte, sepConj_assoc]
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (vvc1_cons_placed hC x s0 s R q cap ptr
        (A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 x.enc.length) (cap.toNat - x.enc.length))
        hpos (by omega) hq hs0_align (Entails.trans (Entails.of_eq (by ac_rfl)) hfold)
        hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace hvregs hcl)

/-! ## Entry and Top-Level Contract -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_entry_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp)
    (hpc : s0.pc = lsmpl.base 117) (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src) (hx2 : s0.readReg64 .x2 = 1#64) :
    SepWPpLsCl lsmpl ((blkPC_117).rebase (blkPl_117).base H) (s0.readReg64 Reg.lr) s0
      (arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt s0.sp vecVecClone1StackX)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hcl
  have hshim := hC.alloc.shim (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  have halloc := hC.alloc.alloc (callerProg := (blkPC_117).rebase (blkPl_117).base H)
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = 1#64 := hx2
  have hpanic248 := fun s P => vvc1_panic_248_placed (A := A) (H := H) hC (Q := vvc1Q A x s0 R) x s0 s P R
  have hafter := fun s' q => vvc1_after_alloc_placed (A := A) (H := H) hC x s0 s' R q hs0_align
  change s0.pc = (blkPl_117).base at hpc
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96 hs0_align (by decide)
  rw [vvc1_stack_split s0.sp]; unfold vvc1Cells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => ?_
  apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_117).base + bv% (52))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl hcl_shim (mid := (blkPl_117).base + bv% (56))
  wp_steps; wp_call hshim_state (); apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay24 : LayoutOk 24 8 := ⟨by decide, hpow8, by decide⟩
  apply sepWPp_of_sepWP_lscl hcl_alloc (mid := (blkPl_117).base + bv% (68))
  wp_steps; wp_call halloc_state (24, 8)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply sepWPp_of_sepWP_lscl hcl_post_alloc (mid := (blkPl_117).base + bv% (248))
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hcl_panic
    refine hpanic248 _ _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_ hcl_panic
    simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace1⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [hsp_sf]; unfold vvc1Saved; ac_rfl))
      (hafter sf_1 (sf_1.readReg64 (Reg.gpr 0#5)) hoom64 ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ hcl_post_alloc)
    all_goals simp only [wp_norm, arm64_norm, *]

/-- `<Vec<Vec<u8>> as Clone>::clone` on `len = 1` satisfies `withLsCodeLoaded lsmpl (vecVecClone1SpecX A)`
at `lsmpl.base 117`. -/
theorem vecVecClone1_placed_okX_of_ser [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H) :
    VecVecClone1PlacedOkStmt A H := by
  unfold VecVecClone1PlacedOkStmt
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  intro x R s0 hpc hrun hpre hs0_align
  simp only [vecVecClone1SpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hm⟩ := hpre
  exact ⟨_, R, by simpa only [sepConj_assoc] using hm,
    vvc1_entry_placed hC x s0 R hpc hrun hs0_align hx0 hx1 hx2⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
