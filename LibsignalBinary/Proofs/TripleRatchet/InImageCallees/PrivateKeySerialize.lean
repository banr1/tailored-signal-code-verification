/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContracts
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `PrivateKey::serialize`

Proves that `<libsignal_core::curve::PrivateKey>::serialize` allocates a 32-byte `Vec<u8>`
copy of the private key bytes, satisfying `privSerializeSpec` and `privSerializeSpecX`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSession
open CryptoVerification.InImageLift

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace PrivateKeySerializeFacts

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem alloc_fnOff : libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "__rustc::__rust_alloc")

theorem privSerialize_fnOff : libsignalSessionCode.fnOff privSerializeName = num% (ls_off% "<libsignal_core::curve::PrivateKey>::serialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::serialize")

end PrivateKeySerializeFacts

open PrivateKeySerializeFacts

namespace PrivateKeySerialize

private theorem allocFailedIn_of_eq {s0 sf : State} (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

private theorem stackAt_privSerialize_opt {hookStack padBelow totalStack : Nat}
    (htot : (hookStack + padBelow) + 32 = totalStack) (hstack : totalStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp totalStack =
      memRegion (sp - 32#64 - BitVec.ofNat 64 (hookStack + padBelow)) padBelow ∗
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  subst htot
  rw [stackAt_split_cells sp (hookStack + padBelow) 4 hstack,
    stackAt_split_bottom (sp - 32#64) hookStack padBelow (by omega),
    sepConj_assoc]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u2) ∗ ((a + 16#64) ↦₆₄ u1) ∗ ((a + 24#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

open ProofLib.ProgramReflection

private gen_decodes libsignalSessionCode_tree privateKeySerializeBin [(ls_off% "<libsignal_core::curve::PrivateKey>::serialize") → (ls_off% "<libsignal_core::curve::PrivateKey>::serialize" + 80)]

def privSerializeSpecWithStack (A : RustAlloc) (totalStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (k, bs, ret) s =>
    ⌜s.readReg64 .x0 = k ∧ s.readReg64 .x8 = ret ∧ bs.length = 32⌝ ∗ (k ↦ₛ bs) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt s.sp totalStack
  post := fun (k, bs, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ vecU8 A ret bs ∗ A.pool ∗ stackAt s0.sp totalStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def privSerializeSpec32WithStack (A : RustAlloc) (totalStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := (privSerializeSpecWithStack A totalStack).pre
  post := fun (k, bs, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗ (∃∗ ptr : BitVec 64, vecU8At A ret 32#64 ptr bs) ∗
      A.pool ∗ stackAt s0.sp totalStack
  onPanic := (privSerializeSpecWithStack A totalStack).onPanic

private theorem privSerializeSpec32WithStack_post_entails (A : RustAlloc) (totalStack : Nat)
    (x : BitVec 64 × List (BitVec 8) × BitVec 64) (s0 sf : State) :
    (privSerializeSpec32WithStack A totalStack).post x s0 sf ⊢
      (privSerializeSpecWithStack A totalStack).post x s0 sf := by
  rcases x with ⟨k, bs, ret⟩
  dsimp only [privSerializeSpec32WithStack, privSerializeSpecWithStack, vecU8]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left
      (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A ret cap ptr bs) 32#64)))

end PrivateKeySerialize

open PrivateKeySerialize

attribute [local irreducible] Program.fnOff

theorem privSerialize_ok_of_contracts_opt (oimg : Option Obj.Image) (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State))
    (hookStack padBelow totalStack : Nat)
    (htot : (hookStack + padBelow) + 32 = totalStack)
    (hstack : totalStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (specWithOptInv oimg (shimSpecWithStack hookStack)))
    (halloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (specWithOptInv oimg (rustAllocSpecWithStack A hookStack)))
    (hpanic : (libsignalSessionCode.rebase b H).externAt?
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) =
      some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName)
      (specWithOptInv oimg (privSerializeSpecWithStack A totalStack)) := by
  refine subroutine_ok_mono (spec := specWithOptInv oimg (privSerializeSpec32WithStack A totalStack)) ?_
    (fun _ _ _ h => h)
    (fun x _ s0 sf h => Satisfies.mono (sepConj_mono_left (privSerializeSpec32WithStack_post_entails A totalStack x s0 sf)) h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  unfold specWithOptInv
  simp only [privSerializeSpec32WithStack, privSerializeSpecWithStack, memRegion_24_cells,
    stackAt_privSerialize_opt htot hstack, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff privSerializeName = num% (ls_off% "<libsignal_core::curve::PrivateKey>::serialize") :=
    privSerialize_fnOff
  code_fetches CryptoVerification.libsignalSessionCode
    privateKeySerializeBin b H hfn (num% (ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) 84
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr privSerializeName = entry
  generalize_entry (libsignalSessionCode.rebase b H) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨k, bs, ret⟩ := x
  dsimp only at *
  have hinv0 : OptCallInv oimg s0 := by assumption
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 h
  rw [hkey_cells k]
  have hpow2 : ∃ j, 1 = 2 ^ j := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (36))
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_optImage (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [vecU8At, vecHeader, h,
      (by decide : (32#64 : BitVec 64) = 0 ↔ False),
      ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
      Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
    wp_done

theorem privSerialize_ok_of_contracts (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State))
    (hshim : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) sessionShimSpec)
    (halloc : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) (rustAllocSpec A))
    (hpanic : (libsignalSessionCode.rebase b H).externAt?
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) =
      some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName)
      (privSerializeSpec A) := by
  have hshim_opt : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (specWithOptInv none (shimSpecWithStack allocHookStack)) := by
    apply subroutine_ok_to_optNone
    have h := subroutine_ok_withStack_of_subroutine_ok hshim allocHookStack
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
      dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    exact h.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)
  exact subroutine_ok_of_optNone
    (privSerialize_ok_of_contracts_opt none b A H allocHookStack 12256 extHookStack
      (by decide) (by decide) hshim_opt (subroutine_ok_to_optNone halloc) hpanic)

theorem privSerialize_ok_ext (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hC : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr privSerializeName)
      (privSerializeSpec A) := by
  exact privSerialize_ok_of_contracts b A (Rust.withPanics ext)
    (hC.shim_ok_at privSerializeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) (by fnoff_eq))
    (hC.alloc_ok_at privSerializeName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) (by fnoff_eq))
    (panic_at_handle_error_ext b ext privSerializeName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (by fnoff_eq))

theorem privSerialize_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr privSerializeName)
      (privSerializeSpec A) :=
  privSerialize_ok_ext b A (tripleRatchetExterns C ctl abs)
    (AllocContracts.of_tripleRatchetProgAt b C A ctl abs hA)

theorem privSerialize_ok_of_contracts_x (img : Obj.Image) (A : RustAlloc)
    (H : String → Option (State → State))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hpanic : (libsignalSessionCode.rebase img.base H).externAt?
      ((libsignalSessionCode.rebase img.base H).fnAddr privSerializeName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) =
      some Rust.panicked) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr privSerializeName)
      ((privSerializeSpecX A).inImage img) := by
  have hshim_opt : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr privSerializeName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (specWithOptInv (some img) (shimSpecWithStack extHookStack)) := by
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ ((withStack sessionShimSpec extHookStack).inImage img).pre x s0 ∗ R := by
      dsimp only [specWithOptInv, OptCallInv, Spec.inImage, withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    exact hshim.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)
  exact privSerialize_ok_of_contracts_opt (some img) img.base A H extHookStack 0 privSerializeStackX
    (by decide) (by decide) hshim_opt halloc hpanic

theorem privSerialize_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr privSerializeName)
      ((privSerializeSpecX A).inImage img) := by
  exact privSerialize_ok_of_contracts_x img A (Rust.withPanics ext)
    (hC.shim_ok_at privSerializeName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) extHookStack (by decide) (by decide)
      (by fnoff_eq))
    (hC.alloc_ok_at privSerializeName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize")) (by fnoff_eq))
    (panic_at_handle_error_ext img.base ext privSerializeName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<libsignal_core::curve::PrivateKey>::serialize"))
      (by fnoff_eq))

/-! ## Relocatable per-block proofs (`[LibsignalPlacement]`) -/

private theorem shimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64} (hookStack : Nat)
    (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (shimSpecWithStack hookStack) := by
  have h' := subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, shimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal (fun _ hout => hout)

theorem privSerialize_placed_ok_of_contracts_opt [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hookStack padBelow totalStack : Nat)
    (htot : (hookStack + padBelow) + 32 = totalStack)
    (hstack : totalStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustNoAllocShimSym) (shimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hpanic : ((blkPC_208).rebase (blkPl_208).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpecWithStack A totalStack) := by
  refine subroutine_ok_mono (spec := privSerializeSpec32WithStack A totalStack) ?_
    (fun _ _ _ h => h)
    (fun x _ s0 sf h => Satisfies.mono (sepConj_mono_left (privSerializeSpec32WithStack_post_entails A totalStack x s0 sf)) h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  simp only [privSerializeSpec32WithStack, privSerializeSpecWithStack, memRegion_24_cells,
    stackAt_privSerialize_opt htot hstack, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wpp_init x s0
  obtain ⟨k, bs, ret⟩ := x
  dsimp only at *
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ :=
    exists_unpack64_of_length_32 h
  rw [hkey_cells k]
  have hpow2 : ∃ j, 1 = 2 ^ j := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_208).base + bv% (36))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [vecU8At, vecHeader, h,
      (by decide : (32#64 : BitVec 64) = 0 ↔ False),
      ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
      Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
    wp_done

/-- Relocatable `<libsignal_core::curve::PrivateKey>::serialize` (Block `208`) meets
`privSerializeSpec A`. -/
theorem privSerialize_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpec A) :=
  privSerialize_placed_ok_of_contracts_opt A H allocHookStack 12256 extHookStack
    (by decide) (by decide)
    (shimWithStack_of_noAllocShim allocHookStack (ls_hook_ok_of_mem hshim))
    (ls_hook_ok_of_mem halloc)
    ((ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic)

/-- Relocatable `<libsignal_core::curve::PrivateKey>::serialize` (Block `208`) meets
`privSerializeSpecX A`. -/
theorem privSerialize_placed_ok_x [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpecX A) :=
  privSerialize_placed_ok_of_contracts_opt A H extHookStack 0 privSerializeStackX
    (by decide) (by decide)
    (shimWithStack_of_noAllocShim extHookStack (ls_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (ls_hook_ok_of_mem halloc) (by decide) (by decide))
    ((ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic)

end CryptoVerification.LibsignalTripleRatchet
