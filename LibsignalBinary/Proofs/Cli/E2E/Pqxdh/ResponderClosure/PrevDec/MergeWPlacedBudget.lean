/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlaced
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Handshake `bytes::merge [local#5]` W-Mode Bridges

Defines the unified outer (`bytesMerge3Stack`) budget-threaded specification
`bytesMerge3RawSpecBoth` (covering both `BytesMergeCapOk` `< 2 ^ 63` and unconstrained-capacity
`< 2 ^ 62`), specializations to `bytesMerge3RawSpecW` and `bytesMerge3RawSpec`, and cross-block
caller lifts on Block `514`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
  extract_withLsCodeLoaded lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (vecU8At)
open CryptoVerification.LibsignalProtoCodec (mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded decodeErrorAtStackLen extract_withLsCodeRoLoaded
  keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  BytesMergeCapOk BytesMergeGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (bytesMerge3Stack)
open CryptoVerification.CliHandshake.Placed (blkPl_514 lsProg_514)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (BytesMergeEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3RawSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsBudget (
  bytesMerge3RawSpecW
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlacedBudget (
  bytesMerge3PlacedSpecW
  BytesMerge6PlacedOkExtW
)

/-! ## Unified Budget-Threaded `bytesMerge3RawSpecBoth` Specification -/

/-- Unified outer (`bytesMerge3Stack`) budget-threaded specification supporting both
`BytesMergeCapOk` (`< 2 ^ 63`) and unconstrained-capacity `< 2 ^ 62` (`W`), with `onPanic = ⌜False⌝`
and `onOom = ⌜False⌝`. -/
def bytesMerge3RawSpecBoth {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 63 ∧
      (BytesMergeCapOk x.valCap x.bs.length ∨ x.bs.length < 2 ^ 62) ∧
      FitsEnv M lim st (BytesMergeEnv x)⌝ ∗
      vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
      (x.bufRef ↦₆₄ x.slot) ∗ sliceCursorAt x.slot x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp bytesMerge3Stack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.bufRef ↦₆₄ x.slot) ∗
      (∃∗ evs : List AllocEvent, ⌜BytesMergeEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp bytesMerge3Stack ∗
      match mergeBytes x.wt x.bs with
      | some (v, rest) =>
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
          (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
            ⌜BytesMergeCapOk x.valCap x.bs.length → BytesMergeCapOk cap' rest.length⌝ ∗
              vecU8At A.repAlloc x.valPtr cap' ptr' v) ∗
          sliceCursorAfter x.slot x.ptr x.bs rest
      | none =>
        ⌜sf.readReg64 .x0 ≠ 0#64⌝ ∗ decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
          vecU8At A.repAlloc x.valPtr x.valCap x.valBuf x.valBs ∗
          memRegion x.slot 16 ∗ (x.ptr ↦ₛ x.bs)

abbrev MergePost3Both {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : BytesMergeGhost) (st : M.σ) (s0 : State) (R : SepProp)
    (sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (bytesMerge3RawSpecBoth A lim).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

theorem SepWPp.to_subroutineOutcome3Both_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : BytesMergeGhost} {st : M.σ} {s0 : State} {P R : SepProp}
    (_hsp_align : s0.spAligned = true)
    (hm : s0.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s0.mem)
    (h : SepWPp prog (s0.readReg64 .lr) s0 P
      (MergePost3Both A lim x st s0 R) (fun _ _ => False)) :
    ∃ sf, Steps prog s0 sf ∧
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim))
        (x, st) R s0 sf := by
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hpost, hsp, hcs⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hfalse⟩⟩ :=
    h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨⟨hpc, hsp, hrun⟩, ⟨hsp, hcs⟩, hpost hmf⟩⟩
  · exact False.elim hfalse
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-! ## Specializations to `W` (`< 2 ^ 62`) and `CapOk` (`< 2 ^ 63`) -/

/-- Specialize any `bytesMerge3RawSpecBoth` contract to `bytesMerge3RawSpecW` (`x.bs.length < 2 ^ 62`). -/
theorem subroutine_ok_bytesMerge3W_of_both [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) := by
  apply subroutine_ok_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal
  obtain ⟨_, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpecW, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hw0, hx1, hx2, hlen62, hfits⟩, _⟩ := hpre0
  have hbs_len : x.bs.length < 2 ^ 63 := by omega
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW, bytesMerge3RawSpecBoth] at hpre ⊢
    exact Satisfies.mono
      (Entails.of_eq (by simp only [hw0, hx1, hx2, hlen62, hbs_len, hfits, or_true, and_self]))
      hpre
  refine reaches_pc_mono (subroutine_ok_apply_full hok (x, st) R hpc hrun hpre' hal) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecBoth, bytesMerge3RawSpecW] at hpost ⊢
  rcases hmb : mergeBytes x.wt x.bs with _ | ⟨v, rest⟩
  · simpa only [hmb] using hpost
  · simp only [hmb] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))))
    exact Entails.sepExists_mono fun cap' => Entails.sepExists_mono fun ptr' =>
      Entails.pure_left fun _ => Entails.refl _

/-- Specialize any `bytesMerge3RawSpecBoth` contract to `bytesMerge3RawSpec`
(`BytesMergeCapOk x.valCap x.bs.length` and `x.bs.length < 2 ^ 63`). -/
theorem subroutine_ok_bytesMerge3_of_both [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64}
    (hok : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) := by
  apply subroutine_ok_intro
  intro ⟨x, st⟩ R s0 hpc hrun hpre hal
  obtain ⟨_, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  rw [bytesMerge3RawSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  obtain ⟨⟨hw0, hx1, hx2, hbs_len, hcap, hfits⟩, _⟩ := hpre0
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)).pre (x, st) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpec, bytesMerge3RawSpecBoth] at hpre ⊢
    exact Satisfies.mono
      (Entails.of_eq (by simp only [hw0, hx1, hx2, hbs_len, hcap, hfits, true_or, and_self]))
      hpre
  refine reaches_pc_mono (subroutine_ok_apply_full hok (x, st) R hpc hrun hpre' hal) ?_
  intro sf _ _ ⟨hpost, hcc⟩
  refine ⟨?_, hcc⟩
  dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecBoth, bytesMerge3RawSpec] at hpost ⊢
  rcases hmb : mergeBytes x.wt x.bs with _ | ⟨v, rest⟩
  · simpa only [hmb] using hpost
  · simp only [hmb] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))))))
    exact Entails.sepExists_mono fun cap' => Entails.sepExists_mono fun ptr' =>
      Entails.pure_left fun himp => Entails.pure_right (himp hcap) (Entails.refl _)

/-! ## Cross-Block Caller Lifts and `BytesMerge6Placed514OkExtW` -/

/-- Lift any `withLsCodeRoLoaded` contract on `lsProg_514 H` to any caller block program at
`lsmpl.base 514`. -/
theorem bytes_merge_6_cro_of_514 [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {spec : Spec α}
    (hcallee : subroutine_ok (lsProg_514 H) (blkPl_514).base (withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514) (withLsCodeRoLoaded lsmpl spec) :=
  keys_ls_subroutine_ok_of_block_cro (callerProg := callerProg) hcallee hi

theorem subroutine_ok_withLsCl_of_cro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m) :
    subroutine_ok prog entry (withLsCl lsmpl spec) :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.subroutine_ok_withLsCl_of_cro h hro

theorem bytes_merge_6_w_cro_of_514 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (h514 : subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) :=
  bytes_merge_6_cro_of_514 h514 hi

theorem bytes_merge_6_w_cl_of_514 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m)
    (h514 : subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (bytesMerge3PlacedSpecW A lim) :=
  subroutine_ok_withLsCl_of_cro (bytes_merge_6_w_cro_of_514 h514 hi) hro

theorem bytes_merge_6_w_cro_of_both [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hboth : subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim)) :=
  bytes_merge_6_w_cro_of_514 (subroutine_ok_bytesMerge3W_of_both hboth) hi

theorem bytes_merge_6_w_cl_of_both [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hro : ∀ m, LibsignalCodeLoaded lsmpl m → LibsignalRoLoaded lsmpl m)
    (hboth : subroutine_ok (lsProg_514 H) (blkPl_514).base
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecBoth A lim)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 514)
      (bytesMerge3PlacedSpecW A lim) :=
  subroutine_ok_withLsCl_of_cro (bytes_merge_6_w_cro_of_both hboth hi) hro

/-- Relocatable `[LibsignalPlacement]` budget-threaded W-contract for `bytes::merge [local#5]`
(Block `514`) on `lsProg_518 ext`. -/
def BytesMerge6Placed514OkExtW [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
    (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A lim))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWPlacedBudget
