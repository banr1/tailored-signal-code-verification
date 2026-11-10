/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

theorem libsignalSessionCode_nonempty :
    0 < libsignalSessionCode.code.length :=
  match h : libsignalSessionCode.code with
  | [] => absurd (congrArg List.isEmpty h) (by decide)
  | _ :: _ => Nat.zero_lt_succ _

theorem stk_le_pow64_of_codeLoaded {prog : Program} {m : Memory}
    {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hlen : 0 < prog.code.length)
    (hL : prog.CodeLoaded m)
    (hm : m ⊨ stackAt sp stk ∗ R) : stk ≤ 2 ^ 64 := by
  have hrx : m.perm (prog.base + 0#64) = some Perm.rx :=
    ((Program.codeLoaded_iff.mp hL).2.2 0 hlen).2.1
  by_cases hle : stk ≤ 2 ^ 64
  · exact hle
  · have ha : InRegion (sp - BitVec.ofNat 64 stk) stk (prog.base + 0#64) := by
      unfold InRegion
      have := BitVec.isLt (prog.base + 0#64 - (sp - BitVec.ofNat 64 stk))
      omega
    have hrw : m.perm (prog.base + 0#64) = some Perm.rw :=
      (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk).perm_rw hm ha
    rw [hrx] at hrw
    exact absurd hrw (by decide)

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

abbrev pkShimStack : Nat := extHookStack + 32

theorem stackAt_pkShim (sp : BitVec 64) :
    stackAt sp pkShimStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

theorem memRegion_16_box (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 32, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₃₂ u1) ∗ ((p + 12#64) ↦₈ b0) ∗
        memRegion (p + 13#64) 3) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 4 4 (by decide),
    memRegion_split (p + 8#64 + 4#64) 1 3 (by decide),
    memRegion_one, ProofLib.memRegion_four, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem pkShim_lift_stk {name : String} {vtOff : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hInner : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      (pkShimSpec vtOff A img pkShimStack))
    (hstk : 0x20 + extHookStack ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      (pkShimSpec vtOff A img stk) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre halign hL
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg32 .x1 = x.id⌝ ∗ A.pool ∗ R) := by
      dsimp only [pkShimSpec, Spec.inImage] at hpre
      convert hpre using 1
      ac_rfl
    exact stk_le_pow64_of_codeLoaded (prog := tripleRatchetProgAtExt img.base ext)
      libsignalSessionCode_nonempty hL hm_stk
  have hstk' : pkShimStack ≤ stk := by
    dsimp [pkShimStack]
    omega
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗
        stackAt s0.sp pkShimStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp pkShimStack
      (stk - pkShimStack) (by omega)
    rwa [Nat.add_sub_of_le hstk'] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗ R
  have hpre' : s0.mem ⊨ (pkShimSpec vtOff A img pkShimStack).pre x s0 ∗ R' := by
    dsimp only [pkShimSpec, Spec.inImage, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1
    ac_rfl
  refine (hInner.to_outcome x R' s0 hpc hrun hpre' halign).mono_outcome ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [pkShimSpec, Spec.inImage, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [pkShimSpec, Spec.inImage, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · dsimp only [pkShimSpec, Spec.inImage] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers
