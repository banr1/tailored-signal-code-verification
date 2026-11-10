/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `prost::encoding::skip_field::<&mut &[u8]> [local#1]`

Induction over nesting depth combining all wire-type branch lemmas into the relocatable
`skipField_placed_ok_x` contract for `prost::encoding::skip_field` (block 1).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpecWithStack)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsmpl
   blkPC_1 blkPl_1 blkPC_76 blkPl_76 blkPC_261 blkPl_261 blkPC_293 blkPl_293
   lsRustAllocSym lsRustNoAllocShimSym
   ls_subroutine_ok_of_block subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalProtoCodec
  (skipField)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (SkipFieldGhost decodeErrorHookStackX)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (SkipFieldPlacedOkX decodeVarintSliceSpecX skipFieldSpecGen skipFieldSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
  (decodeVarintSlowSpecX decode_varint_slow_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.BranchesXBudget
  (skipField_depth_zero_placed_ok_x skipField_endGroup_placed_ok_x
   skipField_lengthDelimited_placed_ok_x skipField_sixtyFourBit_placed_ok_x
   skipField_thirtyTwoBit_placed_ok_x skipField_varint_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipField.StartGroupXBudget
  (skipField_startGroup_placed_ok_x)
open LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldLemmasBudget
  (skipFieldSpecAtX subroutine_ok_skipFieldX_imp_lscl subroutine_ok_skipFieldX_or_lscl)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok_x decode_varint_slice_placed_ok_x)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem skipField_at_depth_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFromCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX)))
    (hSlowCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 293)
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)))
    (hSliceCall : subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (lsmpl.base 76)
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim)))
    (depth : Nat) (hdepth : depth < 2 ^ 32) :
    subroutine_ok ((blkPC_1).rebase (blkPl_1).base H)
      (blkPl_1).base
      (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim depth (fun _ => True))) := by
  induction depth with
  | zero => exact skipField_depth_zero_placed_ok_x hFromCall
  | succ d ih =>
    have hrec := ih (by omega)
    have hAll :=
      subroutine_ok_skipFieldX_or_lscl (skipField_varint_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
        (subroutine_ok_skipFieldX_or_lscl (skipField_sixtyFourBit_placed_ok_x hFromCall d hdepth)
          (subroutine_ok_skipFieldX_or_lscl (skipField_lengthDelimited_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth)
            (subroutine_ok_skipFieldX_or_lscl (skipField_startGroup_placed_ok_x hFromCall hSlowCall hSliceCall d hdepth hrec)
              (subroutine_ok_skipFieldX_or_lscl (skipField_endGroup_placed_ok_x hFromCall d hdepth)
                (skipField_thirtyTwoBit_placed_ok_x hFromCall d hdepth)))))
    refine subroutine_ok_skipFieldX_imp_lscl (fun x _ => ?_) hAll
    cases x.wt <;> simp

namespace SkipFieldCalls

theorem skipFieldSpecAtX_reaches_outcome_eq_lscl [LibsignalPlacement]
    {M : AllocCostModel} (prog : Program) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (P : SkipFieldGhost → Prop) (x : SkipFieldGhost) (st : M.σ) (R : SepProp) (s0 : State) :
    reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)) (x, st) R s0 s0 =
      reaches_outcome prog (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)) (x, st) R s0 s0 := by
  have hpost : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)).post (x, st) =
      (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)).post (x, st) := by
    funext s0' sf'
    dsimp only [withLsCodeLoaded, skipFieldSpecAtX, skipFieldSpecX, skipFieldSpecGen, decodeErrorHookStackX]
    cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs <;> rfl
  have hpan : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)).onPanic (x, st) =
      (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)).onPanic (x, st) := rfl
  have hexit : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)).onExit (x, st) =
      (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)).onExit (x, st) := rfl
  have hoom : (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)).onOom (x, st) =
      (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)).onOom (x, st) := rfl
  have hout : ∀ sf,
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim x.depth P)) (x, st) R s0 sf =
      SubroutineOutcome (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)) (x, st) R s0 sf := by
    intro sf; dsimp only [SubroutineOutcome]; rw [hpost, hpan, hexit, hoom]
  exact propext ⟨fun h => h.mono_outcome (fun sf hs => hout sf ▸ hs),
    fun h => h.mono_outcome (fun sf hs => (hout sf).symm ▸ hs)⟩

theorem subroutine_ok_skipFieldSpecX_of_at_depth_lscl [LibsignalPlacement]
    {M : AllocCostModel} {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : ∀ depth, depth < 2 ^ 32 →
      subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecAtX A lim depth (fun _ => True)))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (skipFieldSpecX A lim)) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  have hpre' := hpre
  dsimp only [withLsCodeLoaded] at hpre' ⊢
  simp only [skipFieldSpecX, skipFieldSpecGen, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hdepth : x.depth < 2 ^ 32 := hpre'.1.2.2.2.2.2.1
  rw [← skipFieldSpecAtX_reaches_outcome_eq_lscl prog A lim (fun _ => True) x st R s0]
  refine (h x.depth hdepth).to_outcome (x, st) R s0 hpc hrun ?_ hsp
  dsimp only [withLsCodeLoaded, skipFieldSpecAtX,
    CryptoVerification.LibsignalTripleRatchet.Prost.skipFieldStackX]
  simp only [sepConj_assoc]
  rw [satisfies_pure_sepConj]
  exact ⟨⟨trivial, trivial, hpre'.1⟩, hpre'.2⟩

end SkipFieldCalls

theorem skipField_placed_ok_of_contracts_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hFrom : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H)
      (blkPl_261).base
      (decodeErrorFromBudgetSpecWithStack M A lim decodeErrorHookStackX))
    (hSlow : subroutine_ok ((blkPC_293).rebase (blkPl_293).base H)
      (blkPl_293).base
      (withLsCodeLoaded lsmpl (decodeVarintSlowSpecX A lim)))
    (hSlice : subroutine_ok ((blkPC_76).rebase (blkPl_76).base H)
      (blkPl_76).base
      (withLsCodeLoaded lsmpl (decodeVarintSliceSpecX A lim))) :
    SkipFieldPlacedOkX A lim H :=
  SkipFieldCalls.subroutine_ok_skipFieldSpecX_of_at_depth_lscl
    (skipField_at_depth_placed_ok_x
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H)
        (subroutine_ok_withLsCodeLoaded_of_plain hFrom))
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlow)
      (ls_subroutine_ok_of_block (callerProg := (blkPC_1).rebase (blkPl_1).base H) hSlice))

theorem skipField_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    SkipFieldPlacedOkX A lim H :=
  skipField_placed_ok_of_contracts_x
    (decode_error_from_placed_ok_x hshim halloc)
    (decode_varint_slow_placed_ok_x hshim halloc)
    (decode_varint_slice_placed_ok_x hshim halloc)

end LibsignalBinary.Proofs.TripleRatchet.Prost.SkipFieldBudget
