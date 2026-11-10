/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetch
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep

/-!
# Budget-Threaded `PreKeySignalMessage::new` Prologue Sequencing and Callee Wrappers

`LibsignalCodeLoaded`-preserving `SepWP`/`SepWPp` sequencing combinators and relocatable
`[LibsignalPlacement]` callee `subroutine_ok` projections on `lsProg_41 H` under
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.IfaceBudgetLemmas (subroutine_ok_rustCliAllocNoOom_externWithStack)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec publicKeySerializeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
  (shimSpecWithStack shimWithStack_of_noAllocShim)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok public_key_serialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (preKeyMsgEncodedLenSpec PreKeyMsgEncodedLenPlacedOk)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement LibsignalCodeLoaded lsmpl withLsCl
   blkPC_205 blkPl_205 lsRustNoAllocShimSym lsRustAllocSym lsMemcpySym
   ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionShimSpec)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41 blkLib_eq_41 blkPl_119)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## `LibsignalCodeLoaded` Sequencing Combinators -/

theorem SepWP.of_sepWP_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded lsmpl sm.mem → SepWP prog ret sm Pm Q)) :
    SepWP prog ret s P Q :=
  SepWP.seq_frozen (fun _ _ hc hk => hc.of_keepsFrozen hk) hcl h

theorem preKeyMsg_seq_wpp_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact hp.elim
  · dsimp only at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem preKeyMsg_seq_wp_lscl [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P1 F : SepProp} {P2 : State → SepProp} {φ : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2 sm)))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → φ sm →
      SepWPp prog ret sm (P2 sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, hoom⟩⟩ := h1.elim hm hL
  · have hmm' : sm.mem ⊨ (P2 sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm hpcm hrunm (hcl.of_keepsFrozen hsteps.keepsFrozen) hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## Relocatable Callee Wrappers -/

theorem subroutine_ok_shimAllocHook_of_sessionShimBudget {prog : Program} {addr : BitVec 64}
    (h : subroutine_ok prog addr sessionShimBudgetSpec) :
    subroutine_ok prog addr (shimSpecWithStack allocHookStack) := by
  refine shimWithStack_of_noAllocShim allocHookStack ?_
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _hL => ?_
  refine h.mono_outcome x R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionShimBudgetSpec, sessionShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [pure_sepConj_pure] at hpost
    exact Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun ⟨hvm, htr⟩ => ⟨htr, hvm⟩)) hpost
  · exact (not_satisfies_false_sepConj hpan).elim
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem public_key_serialize_placed_ok_of_sessionShim [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (publicKeySerializeSpec M A lim) :=
  public_key_serialize_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (subroutine_ok_shimAllocHook_of_sessionShimBudget (ls_hook_ok_of_mem hshim))
    (subroutine_ok_rustCliAllocNoOom_externWithStack (by decide) (by decide)
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem preKeyMsg_shim_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec :=
  ls_hook_ok_of_mem hshim

theorem preKeyMsg_alloc_budget_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
  ls_hook_ok_of_mem halloc

theorem preKeyMsg_alloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)

theorem preKeyMsg_memcpy_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec) :
    subroutine_ok (lsProg_41 H) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec :=
  ls_hook_ok_of_mem hmemcpy

theorem preKeyMsg_publicKeySerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_41 H) (blkPl_205).base
      (withLsCl lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_41 H)
    (public_key_serialize_placed_ok_of_sessionShim hshim halloc)

theorem preKeyMsg_publicKeySerialize_placed_ok_noAllocShim [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (lsProg_41 H) (blkPl_205).base
      (withLsCl lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_41 H)
    (public_key_serialize_placed_ok hshim halloc)

theorem preKeyMsg_encodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hEncLen : PreKeyMsgEncodedLenPlacedOk A H) :
    subroutine_ok (lsProg_41 H) (blkPl_119).base (withLsCl lsmpl (preKeyMsgEncodedLenSpec A)) :=
  ls_subroutine_ok_cl_of_plain (callerProg := lsProg_41 H) hEncLen

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.PrologueFetchBudget
