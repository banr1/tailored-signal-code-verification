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
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1PlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Top-Level Contracts for `encode<EkSentCt1Received> [local#3]` (Block `458`)

Instantiates budget-threaded pinned/unpinned `subroutine_ok` contracts and exact-capacity
`EncodeToVec` bridges for `encode<EkSentCt1Received> [local#3]` on CLI Block `458` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsMemcpySym lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalTripleRatchet (doReserveStack doReserveStackX)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym
   spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (withStepInv)
open CryptoVerification.SpqrV1.Prost.MessageEncode (encodeEkSentCt1ReceivedMsg)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_458 lsProg_458)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.CalleeBridgesBudget
  (etv_ekSentCt1ReceivedEncode_budget_exact_of_exact)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (etvEkSentCt1ReceivedBudgetExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseBudget
  (ekSentCt1ReceivedEncodeExactSpecOf ekSentCt1ReceivedEncodePinnedSpecOfEnv
   ekSentCt1ReceivedPinnedToUnpinned)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBaseStagesBudget
  (EkSentCt1ReceivedEncodeEnvS ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare
   ekSentCt1ReceivedEncodePinnedSpecOfS fitsEnv_ekSentCt1ReceivedEncodeS_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedPlacedCSBudget
  (ekSentCt1ReceivedEncode_unpinned_of_pinned_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
  (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf etv_ekSentCt1ReceivedEncode_exact_of_lscl)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.UnchunkedBasePlacedBudget
  (EkSentCt1ReceivedEncode1PinnedPlacedOk EkSentCt1ReceivedEncode1PinnedPlacedOkExt
   EkSentCt1ReceivedEncode1PinnedPlacedOkExtX EkSentCt1ReceivedEncode1PinnedPlacedOkX
   EkSentCt1ReceivedEncode1PlacedOk EkSentCt1ReceivedEncode1PlacedOkExt
   EkSentCt1ReceivedEncode1PlacedOkExtX EkSentCt1ReceivedEncode1PlacedOkX
   unchunked_authEncode1_cs_placed_ok unchunked_authEncode1_cs_placed_ok_x
   unchunked_doReserve2_cs_placed_ok unchunked_doReserve2_cs_placed_ok_x
   unchunked_ekEncodedLen_cs_placed_ok
   unchunked_encodeVarint2_cs_placed_ok unchunked_encodeVarint2_cs_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1Received1PlacedBudget
  (ekSentCt1ReceivedEncode1_gen_placed_ok)

/-! ## 1. Top-Level `[LibsignalPlacement]` Budget `subroutine_ok` Contracts for Block `458` -/

/-- Unconditional `[LibsignalPlacement]` pinned budget contract for `encode<EkSentCt1Received> [local#3]` (Block `458`). -/
theorem ek_sent_ct1_received_encode_1_pinned_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PinnedPlacedOk A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode1_gen_placed_ok
    (resStack := doReserveStack) (A := A) (lim := lim) (H := H) (by decide)
    (unchunked_ekEncodedLen_cs_placed_ok A.repAlloc s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned budget contract for `encode<EkSentCt1Received> [local#3]` (Block `458`). -/
theorem ek_sent_ct1_received_encode_1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PlacedOk A lim H :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- Unconditional `[LibsignalPlacement]` pinned `doReserveStackX` budget contract for `encode<EkSentCt1Received> [local#3]` (Block `458`). -/
theorem ek_sent_ct1_received_encode_1_pinned_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PinnedPlacedOkX A lim H := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  obtain ⟨P, hP, hwp⟩ := ekSentCt1ReceivedEncode1_gen_placed_ok
    (resStack := doReserveStackX) (A := A) (lim := lim) (H := H) (by decide)
    (unchunked_ekEncodedLen_cs_placed_ok A.repAlloc s0 hcl0)
    (unchunked_encodeVarint2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (unchunked_authEncode1_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc hmc)
    (unchunked_doReserve2_cs_placed_ok_x s0 hcl0 h_panic hshim halloc hrealloc)
    (spqr_hook_ok_of_mem hmc) hpc hrun hpre hsp
  exact ⟨P, R, hP, hwp⟩

/-- Unconditional `[LibsignalPlacement]` unpinned `doReserveStackX` budget contract for `encode<EkSentCt1Received> [local#3]` (Block `458`). -/
theorem ek_sent_ct1_received_encode_1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PlacedOkX A lim H :=
  ekSentCt1ReceivedEncode_unpinned_of_pinned_placed
    (ek_sent_ct1_received_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

theorem ek_sent_ct1_received_encode_1_pinned_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PinnedPlacedOkExt A lim ext :=
  ek_sent_ct1_received_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc

theorem ek_sent_ct1_received_encode_1_placed_ok_ext [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PlacedOkExt A lim ext :=
  ek_sent_ct1_received_encode_1_placed_ok h_panic hshim halloc hrealloc hmc

theorem ek_sent_ct1_received_encode_1_pinned_placed_ok_ext_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PinnedPlacedOkExtX A lim ext :=
  ek_sent_ct1_received_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc

theorem ek_sent_ct1_received_encode_1_placed_ok_ext_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat (Rust.withPanics ext) lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    EkSentCt1ReceivedEncode1PlacedOkExtX A lim ext :=
  ek_sent_ct1_received_encode_1_placed_ok_x h_panic hshim halloc hrealloc hmc

abbrev ekSentCt1ReceivedEncode_1_pinned_placed_ok := @ek_sent_ct1_received_encode_1_pinned_placed_ok
abbrev ekSentCt1ReceivedEncode_1_placed_ok := @ek_sent_ct1_received_encode_1_placed_ok
abbrev ekSentCt1ReceivedEncode_1_pinned_placed_ok_x := @ek_sent_ct1_received_encode_1_pinned_placed_ok_x
abbrev ekSentCt1ReceivedEncode_1_placed_ok_x := @ek_sent_ct1_received_encode_1_placed_ok_x

/-! ## 2. `EncodeToVec` Callee Bridges (Block `458`) -/

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

/-- Generic `withStepInv` exact-capacity bridge from `ekSentCt1ReceivedEncodePinnedSpecOfS` to
`etvEkSentCt1ReceivedBudgetExactSpecOf`. -/
theorem etv_ekSentCt1ReceivedEncode_of_spec_s {resStack : Nat}
    {M : AllocCostModel} {prog : Program} {call_pc : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {s0 : State}
    (hek_ok : subroutine_ok prog call_pc
      (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim))) :
    subroutine_ok prog call_pc
      (withStepInv s0 (etvEkSentCt1ReceivedBudgetExactSpecOf resStack A lim)) := by
  refine etv_ekSentCt1ReceivedEncode_budget_exact_of_exact ?_
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, ekSentCt1ReceivedEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hfits : FitsEnv M lim st
      (EkSentCt1ReceivedEncodeEnvS (ekSentCt1ReceivedPinnedToUnpinned x)) :=
    fitsEnv_ekSentCt1ReceivedEncodeS_of_spare hfit
  have hpre' : s.mem ⊨
      (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOfS resStack A lim)).pre (x, st) s ∗ R := by
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOfS,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv0, ⟨hx0, hx1, Or.inl hfit, hfits⟩, hm⟩
  refine hek_ok.mono_outcome (x, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOfS,
      ekSentCt1ReceivedEncodePinnedSpecOfEnv, ekSentCt1ReceivedEncodeExactSpecOf] at hpost ⊢
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left
        (sepConj_mono_right
          (sepConj_mono_right
            (sepConj_mono (elim_exact_cap_ptr hfit)
              (sepConj_mono_left
                (elim_exact_evs (fun _ hev =>
                  ekSentCt1ReceivedEncodeEnvS_eq_nil_of_spare hfit hev))))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

/-- `EncodeToVec` (`etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack`) contract on Block `458`. -/
theorem etv_ekSentCt1ReceivedEncode_1_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_458 H) (blkPl_458).base
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStack A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ek_sent_ct1_received_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX`) contract on Block `458`. -/
theorem etv_ekSentCt1ReceivedEncode_1_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_458 H) (blkPl_458).base
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedBudgetExactSpecOf doReserveStackX A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ek_sent_ct1_received_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStack`) contract on Block `458`. -/
theorem etv_ekSentCt1ReceivedEncode_1_exact_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_458 H) (blkPl_458).base
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStack A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ek_sent_ct1_received_encode_1_pinned_placed_ok h_panic hshim halloc hrealloc hmc)

/-- `EncodeToVec` (`etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStackX`) contract on Block `458`. -/
theorem etv_ekSentCt1ReceivedEncode_1_exact_placed_ok_x [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_458 H) (blkPl_458).base
      (withLsCodeLoaded lsmpl (etvEkSentCt1ReceivedEncodeExactBudgetSpecOf doReserveStackX A lim)) :=
  etv_ekSentCt1ReceivedEncode_exact_of_lscl
    (ek_sent_ct1_received_encode_1_pinned_placed_ok_x h_panic hshim halloc hrealloc hmc)

abbrev etv_ekSentCt1ReceivedEncode_placed_ok := @etv_ekSentCt1ReceivedEncode_1_placed_ok
abbrev etv_ekSentCt1ReceivedEncode_placed_ok_x := @etv_ekSentCt1ReceivedEncode_1_placed_ok_x
abbrev ek_sent_ct1_received_encode_1_exact_placed_ok := @etv_ekSentCt1ReceivedEncode_1_placed_ok
abbrev ek_sent_ct1_received_encode_1_exact_placed_ok_x := @etv_ekSentCt1ReceivedEncode_1_placed_ok_x

end EncodeToVecBridge

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.EkSentCt1ReceivedPlacedBudget
