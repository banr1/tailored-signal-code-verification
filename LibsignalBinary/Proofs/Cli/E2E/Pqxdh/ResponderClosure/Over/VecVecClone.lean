/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.VecVecDefs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SepWPpIn
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<Vec<Vec<u8>> as Clone>::clone` on 1 Element

Proves `VecVecClone1OkStmt img A ext` (`vecVecClone1_okX_of_ser`) from `SerContractsX img A ext` for
`<[Vec<u8>]>::to_vec` (`x2 = 1`), allocating the 24-byte outer buffer and cloning the single inner
`Vec<u8>` (`{0, 1, 0}` when empty, or `__rust_alloc(L, 1)` + `memcpy` when `L > 0`).
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
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal Proofs.libsignal.Hooks2

namespace VvcStateSimp

theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

end VvcStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓] VvcStateSimp.sp_setPC_pre
  VvcStateSimp.sp_setMem_setPC_pre VvcStateSimp.readReg64_setPC_pre
  VvcStateSimp.readReg64_setMem_setPC_pre VvcStateSimp.readReg32_setPC_pre
  VvcStateSimp.readReg32_setMem_setPC_pre
attribute [local wp_norm] calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32 calleeSavedVRegs_writeReg
  calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite calleeSavedVRegs_writeVReg32_ite
  isCalleeSavedVReg updateCalleeSavedVRegs

/-! ## Instruction Fetches and Stub Contracts -/

gen_decodes libsignalSessionCode_tree vvc1Bin [(ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") → (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone" + 260)]

theorem vvc1_fnOff :
    libsignalSessionCode.fnOff vecVecCloneName =
      num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") :=
  (ls_lemma% fnOff "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")

/-- Emits instruction fetch hypotheses `kStart ≤ k < kEnd` for `Vec<Vec<u8>>::clone`. -/
elab "vvc1_fetches " b:term:max ext:term:max hfn:term:max kStart:num kEnd:num : tactic =>
    Lean.Elab.Tactic.withMainContext do
  let k0 := kStart.getNat; let k1 := kEnd.getNat
  let ns ← Lean.getCurrNamespace
  for k in [k0:k1] do
    let byteOff := 4 * k
    let absOff := num% (ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone") + byteOff
    let pfx := "vvc1Bin_decode_" ++ "0x"
    let decName := ns.str (pfx ++ String.ofList (Nat.toDigits 16 absOff))
    let decId := Lean.mkIdent decName
    let byteOffLit := Lean.Syntax.mkNumLit (toString byteOff)
    if k == 0 then
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have := libsignalSessionCode_fetch_fnAddr_entry (b := $b)
          (H := Rust.withPanics $ext) $hfn (by decide) $decId))
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      have := libsignalSessionCode_fetch_fnAddr (b := $b)
        (H := Rust.withPanics $ext) $hfn (k := $byteOffLit) (by decide) $decId))

theorem vvc1_panic_at {b : BitVec 64} {ext : String → Option (State → State)} :
    (SP2Ext b ext).externAt?
      ((SP2Ext b ext).fnAddr vecVecCloneName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext vecVecCloneName
    (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem vvc1_shim_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
      (Stage1X.session2ShimSpecX.inImage img) :=
  hA.shim_ok_at vecVecCloneName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem vvc1_alloc_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : Stage1X.AllocContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
      ((Stage1X.rustAllocSpecWithStack A Stage1X.extHookStack).inImage img) :=
  hA.alloc_ok_at vecVecCloneName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
    (by fnoff_eq)

theorem vvc1_memcpy_ok {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (ls_off% "memcpy" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
      ((sessionMemcpySpec CryptoVerification.LibsignalTripleRatchet.extHookStack).inImage img) :=
  hC.memcpy_ok_at vecVecCloneName (num% (ls_off% "memcpy" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
    (by fnoff_eq)

/-! ## Frame and Heap Helpers -/

/-- Existential 12-cell (`0x60`-byte) callee-saved frame below `sp`. -/
def vvc1Cells (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
  ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
  ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
    ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
    ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
    ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
    ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
    ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
    ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)

/-- Saved `x19..x30` frame cells below `s0.sp` after the prologue. -/
def vvc1Saved (s0 : State) : SepProp :=
  ((s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
  ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5)) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5)) ∗
  ((s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5)) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5)) ∗
  ((s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5)) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5)) ∗
  ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5)) ∗
  ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))

set_option maxRecDepth 500000 in
theorem vvc1_stack_split (sp : BitVec 64) :
    stackAt sp vecVecClone1StackX = stackAt (sp - 96#64) Stage1X.extHookStack ∗ vvc1Cells sp := by
  have h1 := ProofLib.stackAt_split_cells sp Stage1X.extHookStack 12 (by decide)
  have hadd : Stage1X.extHookStack + 8 * 12 = vecVecClone1StackX := by decide
  rw [hadd] at h1
  change stackAt sp vecVecClone1StackX =
    stackAt (sp - 96#64) Stage1X.extHookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 = vvc1Cells sp := by
    unfold vvc1Cells
    cells_unfold
  rw [h1, hc12]

theorem vvc1_saved_cells (s0 : State) : vvc1Saved s0 ⊢ vvc1Cells s0.sp := by
  unfold vvc1Saved vvc1Cells
  exact Entails.sepExists_right (s0.readReg64 (Reg.gpr 29#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 30#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 28#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 27#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 26#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 25#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 24#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 23#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 22#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 21#5)) <|
    Entails.sepExists_right (s0.readReg64 (Reg.gpr 20#5)) <| Entails.sepExists_right (s0.readReg64 (Reg.gpr 19#5)) <|
    Entails.refl _

theorem vvc1_mem24_cells (dst : BitVec 64) :
    memRegion dst 24 =
      (∃∗ d0 : BitVec 64, dst ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (dst + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (dst + 16#64) ↦₆₄ d2) := by
  have h1 := memRegion_split dst 8 16 (by decide)
  have h2 := memRegion_split (dst + 8#64) 8 8 (by decide)
  have hadd : dst + 8#64 + 8#64 = dst + 16#64 := by rw [BitVec.add_assoc]; rfl
  change memRegion dst 24 = memRegion dst 8 ∗ memRegion (dst + 8#64) 16 at h1
  change memRegion (dst + 8#64) 16 = memRegion (dst + 8#64) 8 ∗ memRegion (dst + 8#64 + 8#64) 8 at h2
  rw [h1, h2, hadd, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]

theorem vvc1_allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

def vvc1Q (A : RustAlloc) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX A).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def vvc1Qp (A : RustAlloc) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (vecVecClone1SpecX A).onPanic x s0 sf ∗ R)

/-! ## Allocation-Error Panic Tails (`+0xec`, `+0xf8`) -/

set_option maxRecDepth 500000 in
theorem vvc1_panic_236 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (x : VecVecClone1Ghost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (236))
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q (vvc1Qp A x s0 R) := by
  intro _ _; have hfn := vvc1_fnOff; have hpanic := vvc1_panic_at (b := img.base) (ext := ext)
  vvc1_fetches img.base ext hfn 59 62
  clear hfn; unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr vecVecCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
  wp_steps; apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [vecVecClone1SpecX, allocPanic, sepConj_assoc] using
    allowPanic_panicked (vvc1_allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

set_option maxRecDepth 500000 in
theorem vvc1_panic_248 {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop} (x : VecVecClone1Ghost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (248))
    (hrun : s.status = .Running) (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s P Q (vvc1Qp A x s0 R) := by
  intro _ _; have hfn := vvc1_fnOff; have hpanic := vvc1_panic_at (b := img.base) (ext := ext)
  vvc1_fetches img.base ext hfn 62 65
  clear hfn; unfold SP2Ext at hpc hpanic ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr vecVecCloneName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<alloc::vec::Vec<alloc::vec::Vec<u8>> as core::clone::Clone>::clone"))
  wp_steps; apply SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
  refine SepWPp.panic (by simp only [wp_norm, hrun]) (by simp only [wp_norm]; exact hpanic) fun hm => ?_
  simpa only [vecVecClone1SpecX, allocPanic, sepConj_assoc] using
    allowPanic_panicked (vvc1_allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace])) hm

/-! ## Epilogue (`+0xc8`) -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_epilogue {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64) (F : SepProp)
    (hent : vecHeader x.dst 1#64 q 1#64 ∗ F ⊢
      arrayAt (prevElem A) 24 x.src [x.enc] ∗ (∃∗ q' : BitVec 64, prevVecAt A x.dst 1#64 q' [x.enc]) ∗ A.pool)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (200)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_align : s.spAligned = true) (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst) (hx23 : s.readReg64 (Reg.gpr 23#5) = q)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ F)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro _ _; have hfn := vvc1_fnOff
  vvc1_fetches img.base ext hfn 50 59
  clear hfn; unfold SP2Ext at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr vecVecCloneName = entry
  examples_hide_fetches
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

/-! ## Heap Folds -/

theorem vvc1_src_eq (A : RustAlloc) (src : BitVec 64) (enc : List (BitVec 8)) :
    arrayAt (prevElem A) 24 src [enc] =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
             memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) := by
  simp only [arrayAt, prevElem, vecU8, vecU8At, sepConj_emp]
  congr 1; funext cap; congr 1; funext ptr
  exact sepConj_left_comm _ _ _

theorem vvc1_src_fold (A : RustAlloc) (src cap ptr : BitVec 64) (enc : List (BitVec 8))
    (h : enc.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :
    vecHeader src cap ptr (BitVec.ofNat 64 enc.length) ∗
      (if cap = 0 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ enc) ∗
         memRegion (ptr + BitVec.ofNat 64 enc.length) (cap.toNat - enc.length)) ⊢
      arrayAt (prevElem A) 24 src [enc] := by
  rw [vvc1_src_eq]
  exact Entails.sepExists_right cap <| Entails.sepExists_right ptr <| Entails.pure_right h (Entails.refl _)

theorem vvc1_post_fold (A : RustAlloc) (src dst q : BitVec 64) (enc : List (BitVec 8)) (hq : q ≠ 0#64) :
    vecHeader dst 1#64 q 1#64 ∗ (arrayAt (prevElem A) 24 src [enc] ∗ A.pool ∗ A.live q 24 8 ∗ vecU8 A q enc) ⊢
      arrayAt (prevElem A) 24 src [enc] ∗ (∃∗ q' : BitVec 64, prevVecAt A dst 1#64 q' [enc]) ∗ A.pool := by
  have hpv : vecHeader dst 1#64 q 1#64 ∗ A.live q 24 8 ∗ vecU8 A q enc ⊢
      ∃∗ q' : BitVec 64, prevVecAt A dst 1#64 q' [enc] := by
    refine Entails.sepExists_right q ?_
    rw [prevVecAt_one_eq A dst 1#64 q enc (by decide)]
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    rw [h1, show (1 : Nat) * 24 = 24 from rfl, show ((1 : Nat) - 1) * 24 = 0 from rfl, memRegion_zero, sepConj_emp]
    exact sepConj_mono_right (Entails.pure_right ⟨Nat.le_refl 1, by decide, hq⟩ (Entails.refl _))
  refine Entails.trans (Entails.of_eq (show _ = arrayAt (prevElem A) 24 src [enc] ∗
    (vecHeader dst 1#64 q 1#64 ∗ A.live q 24 8 ∗ vecU8 A q enc) ∗ A.pool by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left hpv)

theorem vvc1_elem_nil (A : RustAlloc) (q : BitVec 64) :
    (q ↦₆₄ 0#64) ∗ ((q + 8#64) ↦₆₄ 1#64) ∗ ((q + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A q [] := by
  unfold vecU8
  refine Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 ?_)
  unfold vecU8At vecHeader
  have h0 : (0#64 : BitVec 64) = 0 := rfl
  simp only [List.length_nil, h0, ↓reduceIte, sepConj_emp]
  exact Entails.trans (Entails.pure_right ⟨Nat.zero_le _, by decide, by decide⟩ (Entails.refl _))
    (Entails.of_eq (sepConj_comm _ _))

theorem vvc1_elem_cons (A : RustAlloc) (q p : BitVec 64) (enc : List (BitVec 8)) (hp : p ≠ 0#64)
    (hpos : 0 < enc.length) (hlt : enc.length < 2 ^ 63) :
    (q ↦₆₄ BitVec.ofNat 64 enc.length) ∗ ((q + 8#64) ↦₆₄ p) ∗ ((q + 16#64) ↦₆₄ BitVec.ofNat 64 enc.length) ∗
      A.live p enc.length 1 ∗ (p ↦ₛ enc) ⊢ vecU8 A q enc := by
  unfold vecU8
  refine Entails.sepExists_right (BitVec.ofNat 64 enc.length) (Entails.sepExists_right p ?_)
  have hL : (BitVec.ofNat 64 enc.length).toNat = enc.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hne : ¬ (BitVec.ofNat 64 enc.length = 0) := by
    intro h
    have h2 := congrArg BitVec.toNat h
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hL, h0] at h2; omega
  unfold vecU8At vecHeader
  simp only [hne, ↓reduceIte, hL, Nat.sub_self, memRegion_zero, sepConj_emp]
  exact Entails.trans (Entails.of_eq (by simp only [sepConj_assoc]))
    (sepConj_mono_right (Entails.pure_right ⟨Nat.le_refl _, hlt, hp⟩ (Entails.refl _)))

theorem vvc1_finish {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64) (hq : q ≠ 0#64)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (200)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsp_align : s.spAligned = true) (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64)
    (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst) (hx23 : s.readReg64 (Reg.gpr 23#5) = q)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion x.dst 24 ∗ vvc1Saved s0 ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗
        arrayAt (prevElem A) 24 x.src [x.enc] ∗ A.pool ∗ A.live q 24 8 ∗ vecU8 A q x.enc)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) :=
  vvc1_epilogue x s0 s R q _ (vvc1_post_fold A x.src x.dst q x.enc hq) hpc hrun hsp hsp_align hx19 hx20
    hx23 htrace hvregs

/-! ## Post-Outer-Allocation Branches -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
/-- Empty-element branch (`L = 0`): writes `{0, 1, 0}` at `q` without inner allocation. -/
theorem vvc1_nil {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q cap ptr : BitVec 64) (SRC : SepProp)
    (henc : x.enc = []) (hq : q ≠ 0#64) (hs0_align : s0.spAligned = true)
    (hsrc : vecHeader x.src cap ptr 0#64 ∗ SRC ⊢ arrayAt (prevElem A) 24 x.src [x.enc])
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr 0#64 ∗ SRC ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗ A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hfl hsym; have hfn := vvc1_fnOff
  have hfin := fun s' => vvc1_finish (img := img) (A := A) (ext := ext) x s0 s' R q hq
  vvc1_fetches img.base ext hfn 17 32
  clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr vecVecCloneName = entry
  examples_hide_fetches
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96 hs0_align (by decide)
  rw [vvc1_mem24_cells q]; unfold vecHeader
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 => SepWPp.exists_elim fun e2 => ?_
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (200))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_ep hsym_ep
  refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfl_ep hsym_ep)
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
/-- Non-empty element branch (`L > 0`): allocates `p'` (`L` bytes, align 1), copies `ptr` into `p'`,
and writes `{L, p', L}` at `q`. -/
theorem vvc1_cons {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp)
    (q cap ptr : BitVec 64) (SRCM : SepProp)
    (hpos : 0 < x.enc.length) (hlt : x.enc.length < 2 ^ 63) (hq : q ≠ 0#64) (hs0_align : s0.spAligned = true)
    (hsrc : vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ⊢
      arrayAt (prevElem A) 24 x.src [x.enc])
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (vecHeader x.src cap ptr (BitVec.ofNat 64 x.enc.length) ∗ (ptr ↦ₛ x.enc) ∗ SRCM ∗
        memRegion x.dst 24 ∗ A.pool ∗ stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗
        A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hfl hsym; have hfn := vvc1_fnOff; have hshim := vvc1_shim_ok hC.alloc
  have halloc := vvc1_alloc_ok hC.alloc; have hmemcpy := vvc1_memcpy_ok hC
  have hpanic236 := fun s' P => vvc1_panic_236 (img := img) (A := A) (ext := ext) (Q := vvc1Q A x s0 R) x s0 s' P R
  have hfin := fun s' => vvc1_finish (img := img) (A := A) (ext := ext) x s0 s' R q hq
  dsimp only [Stage1X.session2ShimSpecX] at hshim; vvc1_fetches img.base ext hfn 17 50; clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr vecVecCloneName = entry
  examples_hide_fetches
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
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (132))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_shim hsym_shim
  have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (136))
  wp_steps; wp_call hshim_state (); apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_alloc hsym_alloc
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (148))
  wp_steps; wp_call halloc_state (x.enc.length, 1)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (236))
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_panic hsym_panic
    refine hpanic236 _ _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_ hfl_panic hsym_panic
    simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace1⟩ => ?_
    have hmemcpy_state := memcpy_ok_at_stateX hmemcpy hfl_post_alloc hsym_post_alloc
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (200))
    wp_steps; wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), ptr, x.enc)
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_ep hsym_ep
    refine SepWPp.weaken_pre ?_ (hfin _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfl_ep hsym_ep)
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
theorem vvc1_after_alloc {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) (x : VecVecClone1Ghost) (s0 s : State) (R : SepProp) (q : BitVec 64)
    (hs0_align : s0.spAligned = true) (hq : q ≠ 0#64)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName + bv% (68)) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hx0 : s.readReg64 (Reg.gpr 0#5) = q)
    (hx19 : s.readReg64 (Reg.gpr 19#5) = 1#64) (hx20 : s.readReg64 (Reg.gpr 20#5) = x.dst)
    (hx21 : s.readReg64 (Reg.gpr 21#5) = 24#64) (hx22 : s.readReg64 (Reg.gpr 22#5) = x.src)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 (Reg.gpr 30#5)) s
      (arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt (s0.sp - 96#64) Stage1X.extHookStack ∗ vvc1Saved s0 ∗ A.live q 24 8 ∗ memRegion q 24)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hfl hsym
  rw [vvc1_src_eq]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  refine SepWPp.pure_elim fun ⟨hlen, hcap63, hptr⟩ => ?_
  by_cases henc : x.enc = []
  · have hL : BitVec.ofNat 64 x.enc.length = 0#64 := by rw [henc]; rfl
    rw [hL]
    refine vvc1_nil x s0 s R q cap ptr _ henc hq hs0_align ?_ hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace
      hvregs hfl hsym
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
      (vvc1_cons hC x s0 s R q cap ptr
        (A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 x.enc.length) (cap.toNat - x.enc.length))
        hpos (by omega) hq hs0_align (Entails.trans (Entails.of_eq (by ac_rfl)) hfold)
        hpc hrun hsp hx0 hx19 hx20 hx21 hx22 htrace hvregs hfl hsym)

/-! ## Entry -/

set_option maxRecDepth 500000 in
set_option maxHeartbeats 1200000 in
theorem vvc1_entry {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hC : SerContractsX img A ext) (x : VecVecClone1Ghost) (s0 : State) (R : SepProp)
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr vecVecCloneName) (hrun : s0.status = .Running)
    (hs0_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src) (hx2 : s0.readReg64 .x2 = 1#64) :
    SepWPpIn img (SP2Ext img.base ext) (s0.readReg64 Reg.lr) s0
      (arrayAt (prevElem A) 24 x.src [x.enc] ∗ memRegion x.dst 24 ∗ A.pool ∗
        stackAt s0.sp vecVecClone1StackX)
      (vvc1Q A x s0 R) (vvc1Qp A x s0 R) := by
  intro hfl hsym; have hfn := vvc1_fnOff; have hshim := vvc1_shim_ok hC.alloc; have halloc := vvc1_alloc_ok hC.alloc
  have hx0' : s0.readReg64 (Reg.gpr 0#5) = x.dst := hx0
  have hx1' : s0.readReg64 (Reg.gpr 1#5) = x.src := hx1
  have hx2' : s0.readReg64 (Reg.gpr 2#5) = 1#64 := hx2
  have hpanic248 := fun s P => vvc1_panic_248 (img := img) (A := A) (ext := ext) (Q := vvc1Q A x s0 R) x s0 s P R
  have hafter := fun s' q => vvc1_after_alloc (img := img) (A := A) (ext := ext) hC x s0 s' R q hs0_align
  dsimp only [Stage1X.session2ShimSpecX] at hshim; vvc1_fetches img.base ext hfn 0 18; clear hfn
  generalize_entry (SP2Ext img.base ext).fnAddr vecVecCloneName = entry
  examples_hide_fetches
  have hsp_sub_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 96 hs0_align (by decide)
  rw [vvc1_stack_split s0.sp]; unfold vvc1Cells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun v0 => SepWPp.exists_elim fun v1 => SepWPp.exists_elim fun v2 => SepWPp.exists_elim fun v3 =>
    SepWPp.exists_elim fun v4 => SepWPp.exists_elim fun v5 => SepWPp.exists_elim fun v6 => SepWPp.exists_elim fun v7 =>
    SepWPp.exists_elim fun v8 => SepWPp.exists_elim fun v9 => SepWPp.exists_elim fun v10 => SepWPp.exists_elim fun v11 => ?_
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl hsym (mid := entry + bv% (52))
  wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_shim hsym_shim
  have hshim_state := shim_ok_at_stateX hshim hfl_shim hsym_shim
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_shim hsym_shim (mid := entry + bv% (56))
  wp_steps; wp_call hshim_state (); apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_alloc hsym_alloc
  have halloc_state := alloc_ok_at_stateX halloc hfl_alloc hsym_alloc
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay24 : LayoutOk 24 8 := ⟨by decide, hpow8, by decide⟩
  apply CryptoVerification.SepWPp.of_sepWP_inv hfl_alloc hsym_alloc (mid := entry + bv% (68))
  wp_steps; wp_call halloc_state (24, 8)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_post_alloc hsym_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply CryptoVerification.SepWPp.of_sepWP_inv hfl_post_alloc hsym_post_alloc (mid := entry + bv% (248))
    wp_steps; apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]); intro hfl_panic hsym_panic
    refine hpanic248 _ _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_ hfl_panic hsym_panic
    simp only [wp_norm, arm64_norm, *]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod1, htrace1⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by rw [hsp_sf]; unfold vvc1Saved; ac_rfl))
      (hafter sf_1 (sf_1.readReg64 (Reg.gpr 0#5)) hoom64 ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_ ?_ ?_ hfl_post_alloc hsym_post_alloc)
    all_goals simp only [wp_norm, arm64_norm, *]

/-! ## Top-Level Contract -/

/-- `<Vec<Vec<u8>> as Clone>::clone` on `len = 1` satisfies `vecVecClone1SpecX A` on
`SP2Ext img.base ext`. -/
theorem vecVecClone1_okX_of_ser {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : SerContractsX img A ext) :
    VecVecClone1OkStmt img A ext := by
  unfold VecVecClone1OkStmt
  apply subroutine_ok_inImage_of_sepWPpIn
  intro x R s0 hpc hrun hpre hs0_align
  simp only [vecVecClone1SpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2⟩, hm⟩ := hpre
  exact ⟨_, R, by simpa only [sepConj_assoc] using hm, vvc1_entry hC x s0 R hpc hrun hs0_align hx0 hx1 hx2⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
