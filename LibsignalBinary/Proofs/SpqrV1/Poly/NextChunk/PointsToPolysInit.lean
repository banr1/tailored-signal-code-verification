/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Epilogue
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk`: `points_to_polys` Block A Initialization

**Checked by Lean.**

Verifies OOM panic tails and Block A (`0x6a538..0x6a754`, `+436 -> +976`), which allocates 16
initial 2-byte `Poly::zero()` buffers and scatters their headers into `[fsp + 256 .. fsp + 640)`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.NextChunk

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.ComputeAt
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  LagrangePrepare.sp_setPC_pre LagrangePrepare.sp_setMem_setPC_pre
  LagrangePrepare.readReg64_setPC_pre LagrangePrepare.readReg64_setMem_setPC_pre
  LagrangePrepare.readReg32_setPC_pre LagrangePrepare.readReg32_setMem_setPC_pre
  LagrangePrepare.readReg_setPC_pre LagrangePrepare.readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_two :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] theorem exists_pow_two_eq_eight :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

theorem polyOf_empty_cap1_intro (A : RustAlloc) (addr p : BitVec 64) (hp : p ≠ 0#64) :
    ((addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ p) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
     (A.live p 2 2 ∗ memRegion p 2)) ⊢
    polyOf A addr ⟨[]⟩ := by
  unfold polyOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  refine Entails.sepExists_right 1#64 (Entails.sepExists_right p ?_)
  have h1ne : (1#64 : BitVec 64) ≠ 0#64 := by decide
  have hpure : 0 ≤ (1#64 : BitVec 64).toNat ∧ (1#64 : BitVec 64).toNat * 2 < 2 ^ 63 ∧ p ≠ 0#64 :=
    ⟨by decide, by decide, hp⟩
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, h1ne, ↓reduceIte,
    arrayAt, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  rw [sepConj_pure_left_comm]
  refine Entails.pure_right hpure ?_
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMul]
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_112_split_spills (fsp : BitVec 64) :
    memRegion (fsp + 112#64) 120 ⊢
      ∃∗ u184 : BitVec 64, ∃∗ u192 : BitVec 64, ∃∗ u200 : BitVec 64,
      ∃∗ u208 : BitVec 64, ∃∗ u216 : BitVec 64, ∃∗ u224 : BitVec 64,
        memRegion (fsp + 112#64) 72 ∗
        ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
        ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
        ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 72) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 8) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 184#64),
      ProofLib.memRegion_eight (fsp + 192#64),
      ProofLib.memRegion_eight (fsp + 200#64),
      ProofLib.memRegion_eight (fsp + 208#64),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro u224
  apply Entails.sepExists_elim; intro u216
  apply Entails.sepExists_elim; intro u208
  apply Entails.sepExists_elim; intro u200
  apply Entails.sepExists_elim; intro u192
  apply Entails.sepExists_elim; intro u184
  exact Entails.sepExists_right u184 (Entails.sepExists_right u192
    (Entails.sepExists_right u200 (Entails.sepExists_right u208
      (Entails.sepExists_right u216 (Entails.sepExists_right u224 (Entails.of_eq (by ac_rfl)))))))

theorem memRegion_112_fold_spills (fsp u184 u192 u200 u208 u216 u224 : BitVec 64) :
    memRegion (fsp + 112#64) 72 ∗
    ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
    ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
    ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ⊢
    memRegion (fsp + 112#64) 120 := by
  rw [ProofLib.memRegion_split' (b := fsp + 112#64) (n := 72) (k := 48) (b' := fsp + 184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 184#64) (n := 8) (k := 40) (b' := fsp + 192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 192#64) (n := 8) (k := 32) (b' := fsp + 200#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 200#64) (n := 8) (k := 24) (b' := fsp + 208#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 208#64) (n := 8) (k := 16) (b' := fsp + 216#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 216#64) (n := 8) (k := 8) (b' := fsp + 224#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 184#64),
      ProofLib.memRegion_eight (fsp + 192#64),
      ProofLib.memRegion_eight (fsp + 200#64),
      ProofLib.memRegion_eight (fsp + 208#64),
      ProofLib.memRegion_eight (fsp + 216#64),
      ProofLib.memRegion_eight (fsp + 224#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_right u224
  apply Entails.sepExists_right u216
  apply Entails.sepExists_right u208
  apply Entails.sepExists_right u200
  apply Entails.sepExists_right u192
  apply Entails.sepExists_right u184
  exact Entails.of_eq (by ac_rfl)

/-- One initialized `Poly::zero()` slot (`cap = 1, ptr = p, len = 0`, with a live 2-byte allocation). -/
def zeroPolySlotAt (A : RustAlloc) (addr : BitVec 64) : SepProp :=
  ∃∗ ptr,
    ⌜ptr ≠ 0#64⌝ ∗
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
    A.live ptr 2 2 ∗ memRegion ptr 2

/-- `n` contiguous `zeroPolySlotAt` headers starting at `base` with stride 24. -/
def zeroPolySlotsAt (A : RustAlloc) (base : BitVec 64) : Nat → SepProp
  | 0 => emp
  | n + 1 => zeroPolySlotAt A base ∗ zeroPolySlotsAt A (base + 24#64) n

theorem zeroPolySlotAt_intro (A : RustAlloc) (addr ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    (addr ↦₆₄ 1#64) ∗ ((addr + 8#64) ↦₆₄ ptr) ∗ ((addr + 16#64) ↦₆₄ 0#64) ∗
      (A.live ptr 2 2 ∗ memRegion ptr 2) ⊢
      zeroPolySlotAt A addr := by
  unfold zeroPolySlotAt
  refine Entails.sepExists_right ptr ?_
  exact Entails.pure_right hptr (Entails.of_eq (by ac_rfl))

theorem zeroPolySlotAt_entails_polyOf (A : RustAlloc) (addr : BitVec 64) :
    zeroPolySlotAt A addr ⊢ polyOf A addr ⟨[]⟩ := by
  unfold zeroPolySlotAt
  apply Entails.sepExists_elim; intro ptr
  apply Entails.pure_left; intro hptr
  exact polyOf_empty_cap1_intro A addr ptr hptr

theorem zeroPolySlotsAt_entails_polyListOf (A : RustAlloc) :
    ∀ (n : Nat) (base : BitVec 64),
      zeroPolySlotsAt A base n ⊢ polyListOf A base (List.replicate n ⟨[]⟩)
  | 0, base => by
    simp [zeroPolySlotsAt, polyListOf, arrayAt]
    exact Entails.refl _
  | n + 1, base => by
    simp only [zeroPolySlotsAt, List.replicate_succ, polyListOf, arrayAt, vecHeaderBytes,
      BitVec.ofNat_eq_ofNat]
    exact sepConj_mono (zeroPolySlotAt_entails_polyOf A base)
      (zeroPolySlotsAt_entails_polyListOf A n (base + 24#64))

/-- Universal `alloc::raw_vec::handle_error` panic at stub offset `+59096` (`0x78a5c`). -/
theorem next_chunk_panic_59096 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName +
      bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := polyNextChunkName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by rw [polyNextChunk_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])
  refine SepWPp.panic hrun (by rw [hpc]; exact hpanic) fun hm => ?_
  simpa only [nextChunkOnPanic, sepConj_assoc] using
    allowPanic_panicked (by simp [allocFailedIn, Rust.panicked, arm64_norm, htrace]) hm

theorem sepWPp_panic_of_sepWP_59096 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName +
        bv% (ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_59096 s0 sm P R hpcm hrunm htrm))

/-- OOM panic block at `+0x1244` (`+4676..+4684`, `0x6b5c8..0x6b5d0`: `mov w0, #2; mov w1, #2; bl handle_error`). -/
theorem next_chunk_panic_4676 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4676#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1244 12
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s P R ?_
  rw [hentry]
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4676 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (P R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4676#64) s P
      (fun sm Pm => (Pm ⊢ P) ∧ sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4676 s0 sm P R hpcm hrunm htrm))

/-- OOM panic block at `+0x11dc` (`+4572..+4580`, `0x6b560..0x6b568`:
    `ldp x1, x0, [sp, #0x28]; lsl x0, x0, #2; bl handle_error`). -/
theorem next_chunk_panic_4572 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp v40 v48 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Rest R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x11dc 12
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  refine sepWPp_panic_of_sepWP_59096 s0 s
    (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) R ?_
  rw [hentry]
  wp_steps
  exact SepWP.done (by simp only [wp_norm]) (by simp only [wp_norm, hrun])
    ⟨Entails.refl _, by simpa [wp_norm] using htrace⟩

theorem sepWPp_panic_of_sepWP_4572 {b : BitVec 64} {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (s0 s : State) (fsp v40 v48 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Rest R : SepProp)
    (hwp : SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 4572#64) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) ∧
        sm.sp = fsp ∧
        sm.trace = s0.trace ++ [allocFailedEvent])) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (((fsp + 40#64) ↦₆₄ v40) ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ Rest) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  SepWPp.of_sepWP (SepWP.mono hwp fun sm Pm hpcm hrunm ⟨hPm, hspm, htrm⟩ =>
    SepWPp.weaken_pre hPm (next_chunk_panic_4572 s0 sm fsp v40 v48 hfsp_align Rest R hpcm hrunm hspm htrm))

/-- Block A part 1a (`0x6a538..0x6a56c`, `+436 -> +488`):
    spills `x24` to `[fsp + 8]` (`#0x08`) and performs allocations `0..1` (`2` bytes, align `2`),
    spilling `p0..p1` to `[fsp + 224]` (`#0xe0`) and `[fsp + 216]` (`#0xd8`). -/
theorem blockA_alloc_0_1 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u216 u224 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s2 (p0 p1 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 →
      s2.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 488#64 →
      s2.status = .Running →
      s2.sp = fsp →
      s2.trace = s0.trace →
      calleeSavedVRegs s2 = calleeSavedVRegs s →
      s2.readReg64 .x27 = s.readReg64 .x27 →
      s2.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s2
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")]); simp only [rustAllocSpec] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1b4 52
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4676 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 460#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom0 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr0
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom0, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr0; exact htr0⟩
  · conv => arg 4; simp only [hoom0, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr0⟩
    apply SepWPp.of_sepWP (mid := entry + 484#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom1 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr1
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom1, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr0, h, htrace] at htr1; exact htr1⟩
    · conv => arg 4; simp only [hoom1, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr1⟩
      have hcond1 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom1
      apply SepWPp.of_sepWP (mid := entry + 488#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      have hx24 : s.readReg64 (Reg.gpr 24#5) = s.readReg64 .x24 := rfl
      rw [hsp2, hx24]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom0 hoom1
          (by simp only [wp_norm, hcond1, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr1, h_22, htr0, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1b (`0x6a56c..0x6a59c`, `+488 -> +536`):
    performs allocations `2..3` (`2` bytes, align `2`),
    spilling `p2..p3` to `[fsp + 208]` (`#0xd0`) and `[fsp + 200]` (`#0xc8`). -/
theorem blockA_alloc_2_3 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u200 u208 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s4 (p2 p3 : BitVec 64),
      p2 ≠ 0#64 → p3 ≠ 0#64 →
      s4.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 536#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s →
      s4.readReg64 .x27 = s.readReg64 .x27 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")]); simp only [rustAllocSpec] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x1e8 48
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4676 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 508#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom2 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr2
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom2, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr2; exact htr2⟩
  · conv => arg 4; simp only [hoom2, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr2⟩
    apply SepWPp.of_sepWP (mid := entry + 532#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom3 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr3
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom3, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr2, h, htrace] at htr3; exact htr3⟩
    · conv => arg 4; simp only [hoom3, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr3⟩
      have hcond3 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom3
      apply SepWPp.of_sepWP (mid := entry + 536#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      rw [hsp2]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom2 hoom3
          (by simp only [wp_norm, hcond3, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr3, h_22, htr2, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1c (`0x6a59c..0x6a5cc`, `+536 -> +584`):
    performs allocations `4..5` (`2` bytes, align `2`),
    spilling `p4..p5` to `[fsp + 192]` (`#0xc0`) and `[fsp + 184]` (`#0xb8`). -/
theorem blockA_alloc_4_5 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u184 u192 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s6 (p4 p5 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")]); simp only [rustAllocSpec] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x218 48
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4676 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 556#64)
  wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom4 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr4
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by simp only [wp_norm, hoom4, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr4; exact htr4⟩
  · conv => arg 4; simp only [hoom4, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr4⟩
    apply SepWPp.of_sepWP (mid := entry + 580#64)
    wp_steps; wp_apply; wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom5 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr5
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by simp only [wp_norm, hoom5, beq_self_eq_true, ↓reduceIte]) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr4, h, htrace] at htr5; exact htr5⟩
    · conv => arg 4; simp only [hoom5, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr5⟩
      have hcond5 : ¬(sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
        simpa [beq_iff_eq] using hoom5
      apply SepWPp.of_sepWP (mid := entry + 584#64)
      wp_steps
      apply SepWP.done (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs)
      have hsp2 : sf_2.sp = fsp := by
        simp only [h_23, hsp_sf, h_1, hsp]
      rw [hsp2]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (hcont _
          (sf_1.readReg64 (Reg.gpr 0#5))
          (sf_3.readReg64 (Reg.gpr 0#5))
          hoom4 hoom5
          (by simp only [wp_norm, hcond5, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm]; rw [htr5, h_22, htr4, h, htrace])
          (by simp only [arm64_norm, wp_norm, *])
          (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 1 (`0x6a538..0x6a5cc`, `+436 -> +584`):
    spills `x24` to `[fsp + 8]` (`#0x08`) and performs allocations `0..5` (`2` bytes, align `2`),
    spilling `p0..p5` to `[fsp + 224]` (`#0xe0`) down to `[fsp + 184]` (`#0xb8`). -/
theorem blockA_alloc_0_5 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u184 u192 u200 u208 u216 u224 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s6 (p0 p1 p2 p3 p4 p5 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 → p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_0_1 hA s0 s fsp hfsp_align u8 u216 u224
      (((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗ Frame)
      R hpc hrun hsp htrace ?_)
  intro s2 p0 p1 hp0 hp1 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx29_2
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_2_3 hA s0 s2 fsp hfsp_align u200 u208
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗ Frame)
      R hpc2 hrun2 hsp2 htr2 ?_)
  intro s4 p2 p3 hp2 hp3 hpc4 hrun4 hsp4 htr4 hvregs4 hx27_4 hx29_4
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_4_5 hA s0 s4 fsp hfsp_align u184 u192
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗ Frame)
      R hpc4 hrun4 hsp4 htr4 ?_)
  intro s6 p4 p5 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  rw [hvregs4, hvregs2] at hvregs6
  rw [hx27_2] at hx27_4
  rw [hx29_2] at hx29_4
  rw [hx27_4] at hx27_6
  rw [hx29_4] at hx29_6
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hcont s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6)

/-- Block A part 2 (`0x6a5cc..0x6a644`, `+584 -> +704`):
    performs allocations `6..10` (`2` bytes, align `2`), storing pointers `p6..p10`
    into registers `x21, x22, x19, x28, x20`. -/
theorem blockA_alloc_6_10 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s11 (p6 p7 p8 p9 p10 : BitVec 64),
      p6 ≠ 0#64 → p7 ≠ 0#64 → p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 →
      s11.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 704#64 →
      s11.status = .Running →
      s11.sp = fsp →
      s11.trace = s0.trace →
      calleeSavedVRegs s11 = calleeSavedVRegs s →
      s11.readReg64 .x21 = p6 →
      s11.readReg64 .x22 = p7 →
      s11.readReg64 .x19 = p8 →
      s11.readReg64 .x28 = p9 →
      s11.readReg64 .x20 = p10 →
      s11.readReg64 .x27 = s.readReg64 .x27 →
      s11.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s11
        (A.pool ∗
         (A.live p6 2 2 ∗ memRegion p6 2) ∗
         (A.live p7 2 2 ∗ memRegion p7 2) ∗
         (A.live p8 2 2 ∗ memRegion p8 2) ∗
         (A.live p9 2 2 ∗ memRegion p9 2) ∗
         (A.live p10 2 2 ∗ memRegion p10 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")]); simp only [rustAllocSpec] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x248 120
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4676 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 600#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom6 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr6
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr6; exact htr6⟩
  · conv => arg 4; simp only [hoom6, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr6⟩
    apply SepWPp.of_sepWP (mid := entry + 624#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom7 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr7
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr6, h, htrace] at htr7; exact htr7⟩
    · conv => arg 4; simp only [hoom7, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr7⟩
      apply SepWPp.of_sepWP (mid := entry + 648#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom8 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr8
        refine hpanic4676 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr7, h_22, htr6, h, htrace] at htr8; exact htr8⟩
      · conv => arg 4; simp only [hoom8, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr8⟩
        apply SepWPp.of_sepWP (mid := entry + 672#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom9 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr9
          refine hpanic4676 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr8, h_44, htr7, h_22, htr6, h, htrace] at htr9; exact htr9⟩
        · conv => arg 4; simp only [hoom9, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr9⟩
          apply SepWPp.of_sepWP (mid := entry + 696#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          by_cases hoom10 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr10
            refine hpanic4676 _ _ ?_
            wp_steps
            exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr9, h_66, htr8, h_44, htr7, h_22, htr6, h, htrace] at htr10; exact htr10⟩
          · conv => arg 4; simp only [hoom10, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr10⟩
            have hcond10 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom10
            apply SepWPp.of_sepWP (mid := entry + 704#64)
            wp_steps
            apply SepWP.done (by simp only [wp_norm, hcond10, ↓reduceIte]) (by wp_norm_lhs)
            have hsp8 : sf_8.sp = fsp := by
              simp only [h_89, hsp_sf_3, h_67, hsp_sf_2, h_45, hsp_sf_1, h_23, hsp_sf, h_1, hsp]
            rw [hsp8]
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (hcont _
                (sf_1.readReg64 (Reg.gpr 0#5))
                (sf_3.readReg64 (Reg.gpr 0#5))
                (sf_5.readReg64 (Reg.gpr 0#5))
                (sf_7.readReg64 (Reg.gpr 0#5))
                (sf_9.readReg64 (Reg.gpr 0#5))
                hoom6 hoom7 hoom8 hoom9 hoom10
                (by simp only [wp_norm, hcond10, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; rw [htr10, h_88, htr9, h_66, htr8, h_44, htr7, h_22, htr6, h, htrace])
                (by simp only [arm64_norm, wp_norm, *])
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs))

/-- Block A part 3 (`0x6a644..0x6a6b8`, `+704 -> +820`):
    performs allocations `11..15` (`2` bytes, align `2`), storing pointers `p11..p15`
    into registers `x23, x24, x25, x26, x0` while preserving `x19, x20, x21, x22, x27, x28, x29`. -/
theorem blockA_alloc_11_15 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s16 (p11 p12 p13 p14 p15 : BitVec 64),
      p11 ≠ 0#64 → p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      s16.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 820#64 →
      s16.status = .Running →
      s16.sp = fsp →
      s16.trace = s0.trace →
      calleeSavedVRegs s16 = calleeSavedVRegs s →
      s16.readReg64 .x23 = p11 →
      s16.readReg64 .x24 = p12 →
      s16.readReg64 .x25 = p13 →
      s16.readReg64 .x26 = p14 →
      s16.readReg64 .x0 = p15 →
      s16.readReg64 .x19 = s.readReg64 .x19 →
      s16.readReg64 .x20 = s.readReg64 .x20 →
      s16.readReg64 .x21 = s.readReg64 .x21 →
      s16.readReg64 .x22 = s.readReg64 .x22 →
      s16.readReg64 .x27 = s.readReg64 .x27 →
      s16.readReg64 .x28 = s.readReg64 .x28 →
      s16.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s16
        (A.pool ∗
         (A.live p11 2 2 ∗ memRegion p11 2) ∗
         (A.live p12 2 2 ∗ memRegion p12 2) ∗
         (A.live p13 2 2 ∗ memRegion p13 2) ∗
         (A.live p14 2 2 ∗ memRegion p14 2) ∗
         (A.live p15 2 2 ∗ memRegion p15 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hlayout : LayoutOk 2 2 := ⟨by decide, ⟨1, rfl⟩, by decide⟩
  have hshim := hA.shim_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]); simp only [sessionShimSpec] at hshim
  have halloc := hA.alloc_ok_at polyNextChunkName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")) (by rw [polyNextChunk_fnOff, (ls_stub% "__rustc::__rust_alloc")]); simp only [rustAllocSpec] at halloc
  have hpanic4676 := fun (s : State) (P : SepProp) =>
    @sepWPp_panic_of_sepWP_4676 b ext Q s0 s P R
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x2c0 116
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc hshim halloc hpanic4676 hcont ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + 720#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom11 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64
  · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro htr11
    refine hpanic4676 _ _ ?_
    wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨Entails.refl _, by rw [h, htrace] at htr11; exact htr11⟩
  · conv => arg 4; simp only [hoom11, ↓reduceIte, sepConj_assoc]
    apply sepWPp_pure_mid; intro ⟨_, htr11⟩
    apply SepWPp.of_sepWP (mid := entry + 744#64)
    wp_steps; wp_apply; wp_steps; wp_apply
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom12 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64
    · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro htr12
      refine hpanic4676 _ _ ?_
      wp_steps
      exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.refl _, by rw [h_22, htr11, h, htrace] at htr12; exact htr12⟩
    · conv => arg 4; simp only [hoom12, ↓reduceIte, sepConj_assoc]
      apply sepWPp_pure_mid; intro ⟨_, htr12⟩
      apply SepWPp.of_sepWP (mid := entry + 768#64)
      wp_steps; wp_apply; wp_steps; wp_apply
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom13 : sf_5.readReg64 (Reg.gpr 0#5) = 0#64
      · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro htr13
        refine hpanic4676 _ _ ?_
        wp_steps
        exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.refl _, by rw [h_44, htr12, h_22, htr11, h, htrace] at htr13; exact htr13⟩
      · conv => arg 4; simp only [hoom13, ↓reduceIte, sepConj_assoc]
        apply sepWPp_pure_mid; intro ⟨_, htr13⟩
        apply SepWPp.of_sepWP (mid := entry + 792#64)
        wp_steps; wp_apply; wp_steps; wp_apply
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        by_cases hoom14 : sf_7.readReg64 (Reg.gpr 0#5) = 0#64
        · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro htr14
          refine hpanic4676 _ _ ?_
          wp_steps
          exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.refl _, by rw [h_66, htr13, h_44, htr12, h_22, htr11, h, htrace] at htr14; exact htr14⟩
        · conv => arg 4; simp only [hoom14, ↓reduceIte, sepConj_assoc]
          apply sepWPp_pure_mid; intro ⟨_, htr14⟩
          apply SepWPp.of_sepWP (mid := entry + 816#64)
          wp_steps; wp_apply; wp_steps; wp_apply
          apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          by_cases hoom15 : sf_9.readReg64 (Reg.gpr 0#5) = 0#64
          · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro htr15
            refine hpanic4676 _ _ ?_
            wp_steps
            exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
              ⟨Entails.refl _, by rw [h_88, htr14, h_66, htr13, h_44, htr12, h_22, htr11, h, htrace] at htr15; exact htr15⟩
          · conv => arg 4; simp only [hoom15, ↓reduceIte, sepConj_assoc]
            apply sepWPp_pure_mid; intro ⟨_, htr15⟩
            have hcond15 : ¬(sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = true := by
              simpa [beq_iff_eq] using hoom15
            apply SepWPp.of_sepWP (mid := entry + 820#64)
            wp_steps
            apply SepWP.done (by simp only [wp_norm, hcond15, ↓reduceIte]) (by wp_norm_lhs)
            have hsp8 : sf_8.sp = fsp := by
              simp only [h_89, hsp_sf_3, h_67, hsp_sf_2, h_45, hsp_sf_1, h_23, hsp_sf, h_1, hsp]
            rw [hsp8]
            refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
              (hcont _
                (sf_1.readReg64 (Reg.gpr 0#5))
                (sf_3.readReg64 (Reg.gpr 0#5))
                (sf_5.readReg64 (Reg.gpr 0#5))
                (sf_7.readReg64 (Reg.gpr 0#5))
                (sf_9.readReg64 (Reg.gpr 0#5))
                hoom11 hoom12 hoom13 hoom14 hoom15
                (by simp only [wp_norm, hcond15, ↓reduceIte]) (by wp_norm_lhs) (by wp_norm_lhs)
                (by simp only [arm64_norm, wp_norm]; rw [htr15, h_88, htr14, h_66, htr13, h_44, htr12, h_22, htr11, h, htrace])
                (by simp only [arm64_norm, wp_norm, *])
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
                (by wp_norm_lhs) (by wp_norm_lhs))

theorem sepWP_cells_succ {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {k : Nat} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target_pc s (cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest)) post) :
    SepWP prog target_pc s (cells a (k + 1) ∗ Rest) post := by
  have heq : cells a (k + 1) ∗ Rest = ∃∗ v : BitVec 64, cells (a + 8#64) k ∗ ((a ↦₆₄ v) ∗ Rest) := by
    rw [ProofLib.cells_succ, sepExists_sepConj_left]
    exact congrArg sepExists (funext fun v => by ac_rfl)
  rw [heq]
  exact ProofLib.SepWP.exists_left h

theorem sepWP_cells_zero {prog : Program} {target_pc : BitVec 64} {s : State}
    {a : BitVec 64} {Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s Rest post) :
    SepWP prog target_pc s (cells a 0 ∗ Rest) post := by
  rw [ProofLib.cells_zero, emp_sepConj]
  exact h

theorem align_pre {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {Q : State → Prop}
    (h : P ⊢ P')
    (hwp : SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target_pc s P (fun sm Pm => (Pm ⊢ P') ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1, h2⟩ => ⟨Entails.trans h1 h, h2⟩

/-- Block A part 4 (`0x6a6b8..0x6a754`, `+820 -> +976`):
    scatters the 16 `Poly::zero()` headers (`cap = 1, ptr = p_k, len = 0`) into `[fsp + 256 .. fsp + 640)`,
    reloads `x19` from `[fsp + 88]`, sets `x20 = 0`, `x28 = 24`, and folds into
    `polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`. -/
theorem blockA_init_scatter {b : BitVec 64}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (s : State) (fsp vecsBase : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0#64) (hp1 : p1 ≠ 0#64) (hp2 : p2 ≠ 0#64) (hp3 : p3 ≠ 0#64)
    (hp4 : p4 ≠ 0#64) (hp5 : p5 ≠ 0#64) (hp6 : p6 ≠ 0#64) (hp7 : p7 ≠ 0#64)
    (hp8 : p8 ≠ 0#64) (hp9 : p9 ≠ 0#64) (hp10 : p10 ≠ 0#64) (hp11 : p11 ≠ 0#64)
    (hp12 : p12 ≠ 0#64) (hp13 : p13 ≠ 0#64) (hp14 : p14 ≠ 0#64) (hp15 : p15 ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = p15)
    (hx19 : s.readReg64 .x19 = p8)
    (hx20 : s.readReg64 .x20 = p10)
    (hx21 : s.readReg64 .x21 = p6)
    (hx22 : s.readReg64 .x22 = p7)
    (hx23 : s.readReg64 .x23 = p11)
    (hx24 : s.readReg64 .x24 = p12)
    (hx25 : s.readReg64 .x25 = p13)
    (hx26 : s.readReg64 .x26 = p14)
    (hx28 : s.readReg64 .x28 = p9) :
    SepWP (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64)
      s
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          ((fsp + 88#64) ↦₆₄ vecsBase) ∗
          ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
          ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
          polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = vecsBase ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = 24#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29) := by
  poly_next_chunk_fetches_range b (Rust.withPanics ext) 0x334 156
  dsimp only [tripleRatchetProgAtExt, polyNextChunkName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry hentry :
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName = entry
  examples_hide_fetches
  rw [show
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame) =
      (cells (fsp + 256#64) 48 ∗
       (((fsp + 88#64) ↦₆₄ vecsBase) ∗
        ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
        ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
        ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
        (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
        (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
        (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
        (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
        (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
        (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
        (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
        (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
        Frame)) by ac_rfl]
  iterate 48 (apply sepWP_cells_succ; intro _)
  apply sepWP_cells_zero
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, rfl, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (zeroPolySlotsAt_entails_polyListOf A 16 (fsp + 256#64))))))))))
  dsimp only [zeroPolySlotsAt]
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
  have hz0 := zeroPolySlotAt_intro A (fsp + 256#64) p0 hp0
  have hz1 := zeroPolySlotAt_intro A (fsp + 280#64) p1 hp1
  have hz2 := zeroPolySlotAt_intro A (fsp + 304#64) p2 hp2
  have hz3 := zeroPolySlotAt_intro A (fsp + 328#64) p3 hp3
  have hz4 := zeroPolySlotAt_intro A (fsp + 352#64) p4 hp4
  have hz5 := zeroPolySlotAt_intro A (fsp + 376#64) p5 hp5
  have hz6 := zeroPolySlotAt_intro A (fsp + 400#64) p6 hp6
  have hz7 := zeroPolySlotAt_intro A (fsp + 424#64) p7 hp7
  have hz8 := zeroPolySlotAt_intro A (fsp + 448#64) p8 hp8
  have hz9 := zeroPolySlotAt_intro A (fsp + 472#64) p9 hp9
  have hz10 := zeroPolySlotAt_intro A (fsp + 496#64) p10 hp10
  have hz11 := zeroPolySlotAt_intro A (fsp + 520#64) p11 hp11
  have hz12 := zeroPolySlotAt_intro A (fsp + 544#64) p12 hp12
  have hz13 := zeroPolySlotAt_intro A (fsp + 568#64) p13 hp13
  have hz14 := zeroPolySlotAt_intro A (fsp + 592#64) p14 hp14
  have hz15 := zeroPolySlotAt_intro A (fsp + 616#64) p15 hp15
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7 hz8 hz9 hz10 hz11 hz12 hz13 hz14 hz15
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hz0 (sepConj_mono hz1 (sepConj_mono hz2 (sepConj_mono hz3
          (sepConj_mono hz4 (sepConj_mono hz5 (sepConj_mono hz6 (sepConj_mono hz7
          (sepConj_mono hz8 (sepConj_mono hz9 (sepConj_mono hz10 (sepConj_mono hz11
          (sepConj_mono hz12 (sepConj_mono hz13 (sepConj_mono hz14
          (sepConj_mono_left hz15)))))))))))))))))))))))
  exact Entails.of_eq (by ac_rfl)

/-- Complete Block A (`0x6a538..0x6a754`, `+436 -> +976`):
    allocates 16 2-byte `Poly` buffers, stores `self_ptr` (`x24`) to `[fsp + 8]`,
    initializes `[fsp + 256 .. fsp + 640)` to `polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`,
    restores `[fsp + 112 .. fsp + 232)` to `memRegion (fsp + 112#64) 120`,
    and sets `x19 = vecsBase`, `x20 = 0`, `x28 = 24`. -/
theorem blockA_sepWPp {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {Q : State → SepProp → Prop}
    (hA : AllocContracts b A ext)
    (s0 s : State) (fsp vecsBase u8 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hcont : ∀ s_out,
      s_out.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr polyNextChunkName + 976#64 →
      s_out.status = .Running →
      s_out.sp = fsp →
      s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = vecsBase →
      s_out.readReg64 .x20 = 0#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 88#64) ↦₆₄ vecsBase) ∗
         memRegion (fsp + 112#64) 120 ∗
         polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗
       memRegion (fsp + 112#64) 120 ∗
       memRegion (fsp + 256#64) 384 ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hcells : memRegion (fsp + 256#64) 384 = cells (fsp + 256#64) 48 :=
    ProofLib.memRegion_cells (fsp + 256#64) 48 (by decide)
  rw [hcells]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_112_split_spills fsp))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWPp.exists_elim; intro _)
  rename_i u184 u192 u200 u208 u216 u224
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_0_5 hA s0 s fsp hfsp_align u8 u184 u192 u200 u208 u216 u224
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗ cells (fsp + 256#64) 48 ∗ Frame)
      R hpc hrun hsp htrace ?_)
  intro s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_6_10 hA s0 s6 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗ Frame)
      R hpc6 hrun6 hsp6 htr6 ?_)
  intro s11 p6 p7 p8 p9 p10 hp6 hp7 hp8 hp9 hp10 hpc11 hrun11 hsp11 htr11 hvregs11
    hx21_11 hx22_11 hx19_11 hx28_11 hx20_11 hx27_11 hx29_11
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (blockA_alloc_11_15 hA s0 s11 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ Frame)
      R hpc11 hrun11 hsp11 htr11 ?_)
  intro s16 p11 p12 p13 p14 p15 hp11 hp12 hp13 hp14 hp15 hpc16 hrun16 hsp16 htr16 hvregs16
    hx23_16 hx24_16 hx25_16 hx26_16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx27_16 hx28_16 hx29_16
  rw [hx19_11] at hx19_16
  rw [hx20_11] at hx20_16
  rw [hx21_11] at hx21_16
  rw [hx22_11] at hx22_16
  rw [hx27_11, hx27_6] at hx27_16
  rw [hx28_11] at hx28_16
  rw [hx29_11, hx29_6] at hx29_16
  rw [hvregs11, hvregs6] at hvregs16
  have hscatter := blockA_init_scatter A s16 fsp vecsBase
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    hfsp_align
    (A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
     stackAt fsp allocHookStack ∗ Frame)
    hpc16 hrun16 hsp16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx23_16 hx24_16 hx25_16 hx26_16 hx28_16
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWPp.of_sepWP (SepWP.mono hscatter ?_))
  rintro s_out Pm hpc_out hrun_out ⟨hPm, hsp_out, htr_out, hvregs_out, hx19_out, hx20_out, hx27_out, hx28_out, hx29_out⟩
  rw [htr16] at htr_out
  rw [hvregs16] at hvregs_out
  rw [hx27_16] at hx27_out
  rw [hx29_16] at hx29_out
  refine SepWPp.weaken_pre (Entails.trans hPm ?_)
    (hcont s_out hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out)
  refine Entails.trans (Entails.of_eq (show
    ((fsp + 88#64) ↦₆₄ vecsBase) ∗
    ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
    ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
    ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
    polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
    A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
    stackAt fsp allocHookStack ∗ Frame =
    (memRegion (fsp + 112#64) 72 ∗
     ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
     ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
     ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0)) ∗
    (A.pool ∗ ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ ((fsp + 88#64) ↦₆₄ vecsBase) ∗
     polyListOf A (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
     stackAt fsp allocHookStack ∗ Frame) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (memRegion_112_fold_spills fsp p5 p4 p3 p2 p1 p0)) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Poly.NextChunk
