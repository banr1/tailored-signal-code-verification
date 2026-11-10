/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Top-Level Contracts for `encode<Ct1Sent> [local#3]` (Block `459`)

Instantiates budget-threaded pinned/unpinned `subroutine_ok` contracts and exact-capacity
`EncodeToVec` bridges for `encode<Ct1Sent> [local#3]` on CLI Block `459` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (withStepInv)
open CryptoVerification.SpqrV1.Prost.MessageEncode (encodeCt1SentMsg)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_459 lsProg_459)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_ct1SentEncode_budget_exact_of_exact)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvCt1SentBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ct1SentEncodeExactSpecOf ct1SentEncodePinnedSpecOfEnv ct1SentPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (Ct1SentEncodeEnvS ct1SentEncodeEnvS_eq_nil_of_spare
   ct1SentEncodePinnedSpecOfS fitsEnv_ct1SentEncodeS_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (ct1SentEncode_unpinned_of_pinned_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
  (etvCt1SentEncodeExactBudgetSpecOf etv_ct1SentEncode_exact_of_lscl)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlacedBudget
  (Ct1SentEncode1PinnedPlacedOk Ct1SentEncode1PinnedPlacedOkExt
   Ct1SentEncode1PinnedPlacedOkExtX Ct1SentEncode1PinnedPlacedOkX
   Ct1SentEncode1PlacedOk Ct1SentEncode1PlacedOkExt
   Ct1SentEncode1PlacedOkExtX Ct1SentEncode1PlacedOkX
   unchunked_authEncode1_cs_placed_ok unchunked_authEncode1_cs_placed_ok_x
   unchunked_ct1EncodedLen_cs_placed_ok
   unchunked_doReserve2_cs_placed_ok unchunked_doReserve2_cs_placed_ok_x
   unchunked_encodeVarint2_cs_placed_ok unchunked_encodeVarint2_cs_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1Sent1PlacedBudget
  (ct1SentEncode1_gen_placed_ok)

/-! ## 1. Top-Level `[LibsignalPlacement]` Budget `subroutine_ok` Contracts for Block `459` -/

/-- Unconditional `[LibsignalPlacement]` pinned budget contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PinnedPlacedOk A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode1_gen_placed_ok
    (resStack := doReserveStack) (A := A) (lim := lim) (H := H) (by decide)
    (unchunked_ct1EncodedLen_cs_placed_ok A.repAlloc s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned budget contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PlacedOk A lim H :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- Unconditional `[LibsignalPlacement]` pinned `doReserveStackX` budget contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PinnedPlacedOkX A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ct1SentEncode1_gen_placed_ok
    (resStack := doReserveStackX) (A := A) (lim := lim) (H := H) (by decide)
    (unchunked_ct1EncodedLen_cs_placed_ok A.repAlloc s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned `doReserveStackX` budget contract for `encode<Ct1Sent> [local#3]` (Block `459`). -/
theorem ct1_sent_encode_1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PlacedOkX A lim H :=
  ct1SentEncode_unpinned_of_pinned_placed
    (ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem ct1_sent_encode_1_pinned_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PinnedPlacedOkExt A lim ext :=
  ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PlacedOkExt A lim ext :=
  ct1_sent_encode_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_pinned_placed_ok_ext_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PinnedPlacedOkExtX A lim ext :=
  ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem ct1_sent_encode_1_placed_ok_ext_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    Ct1SentEncode1PlacedOkExtX A lim ext :=
  ct1_sent_encode_1_placed_ok_x h_panic hshim halloc hrealloc hmc

abbrev ct1_sent_encode_1_pinned_placed_ok_uncond := @ct1_sent_encode_1_pinned_placed_ok
abbrev ct1_sent_encode_1_pinned_placed_ok_x_uncond := @ct1_sent_encode_1_pinned_placed_ok_x
abbrev ct1SentEncode_1_pinned_placed_ok := @ct1_sent_encode_1_pinned_placed_ok
abbrev ct1SentEncode_1_placed_ok := @ct1_sent_encode_1_placed_ok
abbrev ct1SentEncode_1_pinned_placed_ok_x := @ct1_sent_encode_1_pinned_placed_ok_x
abbrev ct1SentEncode_1_placed_ok_x := @ct1_sent_encode_1_placed_ok_x

/-! ## 2. `EncodeToVec` Callee Bridges (Block `459`) -/

section EncodeToVecBridge

private theorem elim_exact_cap_ptr {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} (hfit : bs1.length + bs2.length ≤ cap.toNat) :
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜cap.toNat ≤ cap'.toNat ∧ (bs1.length + bs2.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr)⌝ ∗
      vecU8At A v cap' ptr' (bs1 ++ bs2)) ⊢
    vecU8At A v cap ptr (bs1 ++ bs2) :=
  Entails.sepExists_elim fun cap' =>
    Entails.sepExists_elim fun ptr' =>
      Entails.pure_left fun ⟨_, hpres⟩ => by
        obtain ⟨rfl, rfl⟩ := hpres hfit
        exact Entails.refl _

private theorem elim_exact_evs {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {st : M.σ} {sf : State} {P : List AllocEvent → Prop}
    (hnil : ∀ evs, P evs → evs = []) :
    (∃∗ evs : List AllocEvent, ⌜P evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ⊢
    A.pool lim st sf :=
  Entails.sepExists_elim fun evs =>
    Entails.pure_left fun hP => by
      rw [hnil evs hP]
      dsimp only [AllocCostModel.stepEvents]
      exact Entails.refl _

/-- Generic `withStepInv` exact-capacity bridge from `ct1SentEncodePinnedSpecOfS` to
`etvCt1SentBudgetExactSpecOf`. -/
theorem etv_ct1SentEncode_of_spec_s {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hct1_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ct1SentEncodePinnedSpecOfS resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvCt1SentBudgetExactSpecOf resStack A lim)) := by
  refine etv_ct1SentEncode_budget_exact_of_exact ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, ct1SentEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hfits : FitsEnv M lim st (Ct1SentEncodeEnvS (ct1SentPinnedToUnpinned x)) :=
    fitsEnv_ct1SentEncodeS_of_spare hfit
  have hpre' : s.mem ⊨
      (withStepInv s0 (ct1SentEncodePinnedSpecOfS resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOfS, ct1SentEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hfits⟩, hm⟩
  refine hct1_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOfS,
      ct1SentEncodePinnedSpecOfEnv, ct1SentEncodeExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left
                (elim_exact_evs (fun _ hev =>
                  ct1SentEncodeEnvS_eq_nil_of_spare hfit hev))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- `EncodeToVec` (`etvCt1SentBudgetExactSpecOf doReserveStack`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStack A lim)) :=
  etv_ct1SentEncode_exact_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvCt1SentBudgetExactSpecOf doReserveStackX`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_ct1SentEncode_exact_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvCt1SentEncodeExactBudgetSpecOf doReserveStack`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeExactBudgetSpecOf doReserveStack A lim)) :=
  etv_ct1SentEncode_exact_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvCt1SentEncodeExactBudgetSpecOf doReserveStackX`) contract on Block `459`. -/
theorem etv_ct1SentEncode_1_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_459 H) (blkPl_459).base
      (withLsCodeLoaded lsmpl (etvCt1SentEncodeExactBudgetSpecOf doReserveStackX A lim)) :=
  etv_ct1SentEncode_exact_of_lscl
    (ct1_sent_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

abbrev etv_ct1SentEncode_placed_ok := @etv_ct1SentEncode_1_placed_ok
abbrev etv_ct1SentEncode_placed_ok_x := @etv_ct1SentEncode_1_placed_ok_x
abbrev ct1_sent_encode_1_exact_placed_ok := @etv_ct1SentEncode_1_placed_ok
abbrev ct1_sent_encode_1_exact_placed_ok_x := @etv_ct1SentEncode_1_placed_ok_x

end EncodeToVecBridge

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.Ct1SentPlacedBudget
