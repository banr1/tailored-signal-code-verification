/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Defs
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody

/-!
# Budget-Threaded `PreKeyRecord::deserialize` Callee Wrappers and Epilogue State

`RustCliAllocBudget`-threaded relocatable `[LibsignalPlacement]` callee wrappers and epilogue state
invariants for `PreKeyRecord::deserialize` (Block `65`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed
open CryptoVerification.RecordCodecsBinary (preKeyResultAt ls_subroutine_ok_lscro_of_block
  ls_subroutine_ok_lscro_of_cl ls_subroutine_ok_lscro_of_plain)
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers (PkEpilogueStatePlaced)
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget

theorem pk_varintSlice_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 76)
      (withLsCodeRoLoaded lsmpl (decodeVarintSliceSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.varintSlice

theorem pk_int32Merge_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 8)
      (withLsCodeRoLoaded lsmpl (int32MergeSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.int32Merge

theorem pk_skipField_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 1)
      (withLsCodeRoLoaded lsmpl (skipFieldSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.skipField

theorem pk_dropDecodeError_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 4)
      (withLsCodeRoLoaded lsmpl (dropDecodeErrorSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_65 H) d.dropDecodeError

theorem pk_bytesMerge_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 7)
      (withLsCodeRoLoaded lsmpl (bytesMergeRawSpecX A lim)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_65 H) d.bytesMerge

theorem pk_varintSlow_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 293)
      (withLsCodeRoLoaded lsmpl (decodeVarintSlowSpecWithStack M A lim (64 + 2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.varintSlow

theorem pk_decodeErrorFrom_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromSpecWithStack M A lim (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_65 H) d.decodeErrorFrom

theorem pk_decodeErrorPush_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl
        (decodeErrorPushBoundedExternSpecWithStack M A lim (2 * extHookStack))) :=
  ls_subroutine_ok_lscro_of_cl (callerProg := lsProg_65 H) d.decodeErrorPush

theorem pk_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (d : PortDepsPlaced M A lim H) :
    subroutine_ok (lsProg_65 H) (lsρ lsRustDeallocSym)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  ls_dealloc_lscro_ok (callerProg := lsProg_65 H) d.dealloc

def pkEpilogueMem [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel maxLen : Nat)
    (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError PreKeyRecord) (sf : State) : SepProp :=
  memRegion sp' 160 ∗
    ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
    preKeyResultAt A.repAlloc x19 out ∗
    (ptr ↦ₛ bs) ∗
    (∃∗ evs : List AllocEvent, ⌜PkSubEnv fuel maxLen evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf) ∗
    stackAt sp' (skipFieldStackX 100)

def pkEpiloguePostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel maxLen : Nat)
    (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8))
    (out : Except SignalProtocolError PreKeyRecord) : State → SepProp → Prop :=
  fun sf Pf => PkEpilogueStatePlaced s0 sp' sf ∧
    (Pf ⊢ pkEpilogueMem A lim st fuel maxLen sp' x19 ptr bs out sf)

theorem pkEpiloguePostPlaced_append_prefix [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (fuel maxLen : Nat)
    (s0 : State) (sp' x19 ptr : BitVec 64) (bs : List (BitVec 8)) (k : Nat) (hk : k ≤ bs.length)
    (out : Except SignalProtocolError PreKeyRecord)
    (sf : State) (Pf : SepProp)
    (h : pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 (ptr + BitVec.ofNat 64 k) (bs.drop k) out sf Pf) :
    pkEpiloguePostPlaced A lim st fuel maxLen s0 sp' x19 ptr bs out sf (Pf ∗ (ptr ↦ₛ bs.take k)) := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, ?_⟩
  refine Entails.trans (sepConj_mono_left hent) ?_
  unfold pkEpilogueMem
  rw [← pointsToBytes_take_drop ptr bs k hk]
  apply entails_of_eq
  ac_rfl

theorem pkEpiloguePostPlaced_prepend_iter [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {fuel maxLen : Nat}
    {evs₁ : List AllocEvent} (h1 : RecordCodecIterEnv maxLen evs₁)
    {s0 : State} {sp' x19 ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} {sf : State} {Pf : SepProp}
    (h : pkEpiloguePostPlaced A lim (M.stepEvents evs₁ st) fuel maxLen s0 sp' x19 ptr bs out sf Pf) :
    pkEpiloguePostPlaced A lim st (fuel + 1) maxLen s0 sp' x19 ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold pkEpilogueMem
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.sepExists_elim fun evs₂ => Entails.pure_left fun h2 => ?_
  rw [← M.stepEvents_append]
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [pure_true_emp (PkSubEnv.prepend_iter h1 h2), emp_sepConj]
  exact Entails.refl _

theorem pkEpiloguePostPlaced_prepend_bytes [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {budget maxLen : Nat}
    {wt : WireType} {valCap : BitVec 64} {bsB v rest : List (BitVec 8)} {evs₁ : List AllocEvent}
    (hm : mergeBytes wt bsB = some (v, rest)) (hlen : bsB.length ≤ maxLen)
    (hevs₁ : evs₁ = bytesMergeEventsCore wt valCap bsB)
    {s0 : State} {sp' x19 ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} {sf : State} {Pf : SepProp}
    (h : pkEpiloguePostPlaced A lim (M.stepEvents evs₁ st) budget maxLen s0 sp' x19 ptr bs out sf Pf) :
    pkEpiloguePostPlaced A lim st (budget + 2 * v.length + 1) maxLen s0 sp' x19 ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold pkEpilogueMem
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.sepExists_elim fun evs₂ => Entails.pure_left fun h2 => ?_
  rw [← M.stepEvents_append]
  refine Entails.sepExists_right (evs₁ ++ evs₂) ?_
  rw [pure_true_emp (PkSubEnv.prepend_bytes hm hlen hevs₁ h2), emp_sepConj]
  exact Entails.refl _

theorem pkEpiloguePostPlaced_mono_fuel [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {f₁ f₂ maxLen : Nat}
    (hle : f₁ ≤ f₂)
    {s0 : State} {sp' x19 ptr : BitVec 64} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} {sf : State} {Pf : SepProp}
    (h : pkEpiloguePostPlaced A lim st f₁ maxLen s0 sp' x19 ptr bs out sf Pf) :
    pkEpiloguePostPlaced A lim st f₂ maxLen s0 sp' x19 ptr bs out sf Pf := by
  rcases h with ⟨hst, hent⟩
  refine ⟨hst, Entails.trans hent ?_⟩
  unfold pkEpilogueMem
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left ?_))))
  refine Entails.sepExists_elim fun evs => Entails.pure_left fun hevs => ?_
  refine Entails.sepExists_right evs ?_
  rw [pure_true_emp (hevs.mono_fuel hle), emp_sepConj]
  exact Entails.refl _

end LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.DefsBudget
