/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_realloc")

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_x (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_x (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_x (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_x (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

def rustReallocUninitSpecX (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × Nat) where
  pre := fun (p, old, align, new) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk old align ∧ LayoutOk new align⌝ ∗
      A.pool ∗ A.live p old align ∗ memRegion p old ∗ stackAt s.sp extHookStack
  post := fun (p, old, align, new) s0 sf =>
    A.pool ∗ stackAt s0.sp extHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ memRegion p old
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ memRegion (sf.readReg64 .x0) new)

theorem realloc_uninit_ok_at_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "__rustc::__rust_realloc" := by simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      ((rustReallocUninitSpecX A).inImage img) := by
  refine subroutine_ok.of_codeLoaded fun ⟨p, old, align, new⟩ R s0 hpc hrun hpre hsp _ => ?_
  have hpre' : s0.mem ⊨ ((rustReallocExternSpecWithStack A extHookStack).inImage img).pre
      (p, old, align, new, []) s0 ∗ R := by
    simp only [Spec.inImage, rustReallocExternSpecWithStack, rustReallocUninitSpecX,
      List.length_nil, Nat.zero_le, and_true, pointsToBytes_nil, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_assoc] at hpre ⊢
    exact hpre
  refine (realloc_ok_at_norm_ext_x hA hk).mono_outcome (p, old, align, new, []) R s0 hpc hrun
    hpre' hsp fun sf hout => ?_
  simpa only [SubroutineOutcome, Spec.inImage, rustReallocExternSpecWithStack,
    rustReallocSpecWithStack, rustReallocUninitSpecX, List.length_nil, pointsToBytes_nil,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero, emp_sepConj, sepConj_assoc] using hout

def finishGrow7ZeroSpecX (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧
      0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack
  post := fun (out, _cap, _ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_7_zero_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow7Name)
      ((finishGrow7ZeroSpecX A).inImage img) := by
  unfold Spec.inImage finishGrow7ZeroSpecX
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")
  have hshim := shim_ok_at2_ext_x hA
    (name := finishGrow7Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
  have halloc := alloc_ok_at_norm_ext_x hA
    (name := finishGrow7Name)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) 164
  dsimp only [tripleRatchetProgAtExt, finishGrow7Name] at hshim halloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]" = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hnew_pos : 0 < new.toNat := by assumption
  subst fsp
  subst cap
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcbz := beq_lsl5_zero_eq_false hnew_pos (by omega)
  have hlsl : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow8, by omega⟩
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) hinv0
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (new.toNat * 32, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 1#64
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

def finishGrow7NeSpecX (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      cap.toNat * 32 < 2 ^ 63 ∧ 0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) ∗
    cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack
  post := fun (out, cap, ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

theorem finish_grow_7_ne_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr finishGrow7Name)
      ((finishGrow7NeSpecX A).inImage img) := by
  unfold Spec.inImage finishGrow7NeSpecX
  cells_unfold
  have hfn := (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")
  have hrealloc := realloc_uninit_ok_at_ext_x hA
    (name := finishGrow7Name)
    (k := num% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]"))
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) 164
  dsimp only [tripleRatchetProgAtExt, finishGrow7Name] at hrealloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]" = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  subst fsp
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hlsl_cap : (cap <<< 5).toNat = cap.toNat * 32 := lsl5_toNat (by omega)
  have hlsl_new : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hcap_pos : 0 < cap.toNat := Nat.pos_of_ne_zero fun h0 =>
    hcap_ne (BitVec.eq_of_toNat_eq (by simp [h0]))
  have hlay_old : LayoutOk (cap.toNat * 32) 8 := ⟨by omega, hpow8, by omega⟩
  have hlay : LayoutOk (new.toNat * 32) 8 := ⟨by omega, hpow8, by omega⟩
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_realloc" - ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#6]")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hrealloc (ptr, cap.toNat * 32, 8, new.toNat * 32)
  wp_steps
  wp_if hoom
  · have hoom' : sf.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 0#64
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 1#64
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
