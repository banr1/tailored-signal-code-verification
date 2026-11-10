/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Heap.SpecBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.InImage.Uuid

/-!
# Budget-Threaded Configurable-Stack Hook Contracts

Provides `RustCliAllocBudget` and `VmPreserved`-strengthened `*WithStack`, `*FnSpec`, and
`*AnySpec` contracts and stack-lifting lemmas for allocator operations, Prost `DecodeError`
and slow-varint helpers, `subtle::black_box`, `Uuid::try_parse`, `rng_fill`, AES-256-CBC, and
empty-state `spqr::recv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoGames.CBC (AesKey Block bytesToBlock)
open CryptoGames.HKDF (Salt bytesToKey32)
open CryptoGames.LibsignalSession (aesCbcDecrypt)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (
  AesCall VecArg blackBoxSpec decodeErrorAtStackLen decodeErrorHookStack extHookStack
  spqrRecvResultAt spqrRecvStack uuidResultAt uuidResultAt_entails_any
  uuidTryParseCodeSpec uuidTryParseSpec uuidTryParseStack varintSlow varintSlowStack
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetExternSpecWithStack rustCliAllocBudgetSpecWithStack
  rustCliAllocNoOomExternSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack rustCliDeallocBudgetSpecWithStack
  rustCliDeallocNoOomExternSpecWithStack rustCliDeallocNoOomSpecWithStack
  rustCliReallocBudgetExternSpecWithStack rustCliReallocBudgetSpecWithStack
  rustCliReallocNoOomExternSpecWithStack rustCliReallocNoOomSpecWithStack
  subroutine_ok_rustCliAllocBudget_withStack
  subroutine_ok_rustCliDeallocBudget_externWithStack
  subroutine_ok_rustCliReallocBudget_externWithStack
)
open LibsignalBinary.Heap.SpecBudget (
  DecodeErrorFromEnv DecodeErrorPushEnv aesDecBudgetSpec aesDecFnBudgetSpec aesDecWeakBudgetSpec
  aesEncFnBudgetSpec decodeErrorFromBudgetSpec decodeErrorFromBudgetSpecWithStack
  decodeErrorPushBudgetSpec decodeErrorPushBudgetSpecWithStack withVmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  DecodeVarintSlowEnv decodeVarintSlowBudgetSpec decodeVarintSlowBudgetSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  uuidTryParseBudgetSpec uuidTryParseCodeBudgetSpec
)

/-! ## `withStack` and allocator `*WithStack` aliases -/

abbrev withStack {α : Type} (spec : Spec α) (hookStack : Nat := extHookStack) : Spec α :=
  CryptoVerification.LibsignalTripleRatchet.withStack spec hookStack

theorem subroutine_ok_withStack_of_subroutine_ok {α : Type} {P : Program} {addr : BitVec 64}
    {spec : Spec α} (h : subroutine_ok P addr spec) (hookStack : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr (withStack spec hookStack) :=
  CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok
    h hookStack hpan hex hoom

abbrev rustAllocSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocBudgetSpecWithStack inst
abbrev rustDeallocSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetSpecWithStack inst
abbrev rustDeallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocBudgetExternSpecWithStack inst
abbrev rustReallocSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetSpecWithStack inst
abbrev rustReallocExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocBudgetExternSpecWithStack inst

abbrev rustAllocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomSpecWithStack inst
abbrev rustAllocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliAllocNoOomExternSpecWithStack inst
abbrev rustDeallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomSpecWithStack inst
abbrev rustDeallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliDeallocNoOomExternSpecWithStack inst
abbrev rustReallocNoOomSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomSpecWithStack inst
abbrev rustReallocNoOomExternSpecWithStack [inst : LibsignalPlacement] := @rustCliReallocNoOomExternSpecWithStack inst

abbrev rustAllocWithStack_of_rustAlloc [inst : LibsignalPlacement] := @subroutine_ok_rustCliAllocBudget_withStack inst
abbrev rustDeallocExternWithStack_of_rustDealloc [inst : LibsignalPlacement] := @subroutine_ok_rustCliDeallocBudget_externWithStack inst
abbrev rustReallocExternWithStack_of_rustRealloc [inst : LibsignalPlacement] := @subroutine_ok_rustCliReallocBudget_externWithStack inst

/-! ## Prost `DecodeError` and `decode_varint_slow` `*WithStack` contracts -/

abbrev decodeErrorFromSpecWithStack := @decodeErrorFromBudgetSpecWithStack
abbrev decodeErrorPushSpecWithStack := @decodeErrorPushBudgetSpecWithStack
abbrev decodeVarintSlowSpecWithStack := @decodeVarintSlowBudgetSpecWithStack

/-- Budget-threaded `DecodeError::push` contract with configurable stack budget,
existentializing the updated `Box<Inner>` pointer `e'` in `post`. -/
def decodeErrorPushExternBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ e ≠ 0#64 ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp hookStack
  post := fun (d, _, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ e' : BitVec 64, ⌜e' ≠ 0#64⌝ ∗ (d ↦₆₄ e') ∗
        decodeErrorAtStackLen A.repAlloc e' (n + 1)) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp hookStack

abbrev decodeErrorPushExternSpecWithStack := @decodeErrorPushExternBudgetSpecWithStack

theorem decodeErrorPushExtern_of_decodeErrorPush {M : AllocCostModel}
    {P : Program} {addr : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hookStack : Nat}
    (h : subroutine_ok P addr (decodeErrorPushBudgetSpecWithStack M A lim hookStack)) :
    subroutine_ok P addr (decodeErrorPushExternBudgetSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hpre hal => ?_
  simp only [decodeErrorPushExternBudgetSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, he_ne, hn, hfits⟩, hmem⟩
  have hpre' : s0.mem ⊨
      (decodeErrorPushBudgetSpecWithStack M A lim hookStack).pre (d, e, n, st) s0 ∗ R := by
    simp only [decodeErrorPushBudgetSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hn, hfits⟩, hmem⟩
  refine h.mono_outcome (d, e, n, st) R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [decodeErrorPushBudgetSpecWithStack, decodeErrorPushExternBudgetSpecWithStack,
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    exact ⟨hpost.1, e, he_ne, hpost.2⟩
  · dsimp only [decodeErrorPushBudgetSpecWithStack] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [decodeErrorPushBudgetSpecWithStack] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorPushBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorFromWithStack_of_decodeErrorFrom {M : AllocCostModel}
    {P : Program} {addr : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hookStack : Nat}
    (h : subroutine_ok P addr (decodeErrorFromBudgetSpec M A lim))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorFromBudgetSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨k, w, st⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack
      (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorFromBudgetSpec M A lim).pre (k, w, st) s0 ∗ R' := by
    dsimp only [decodeErrorFromBudgetSpecWithStack, decodeErrorFromBudgetSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (k, w, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorFromBudgetSpecWithStack, decodeErrorFromBudgetSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [decodeErrorFromBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [decodeErrorFromBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorFromBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeErrorPushWithStack_of_decodeErrorPush {M : AllocCostModel}
    {P : Program} {addr : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hookStack : Nat}
    (h : subroutine_ok P addr (decodeErrorPushBudgetSpec M A lim))
    (hle : decodeErrorHookStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeErrorPushBudgetSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨d, e, n, st⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗
        stackAt s0.sp decodeErrorHookStack := by
    have h1 := stackAt_split_bottom s0.sp decodeErrorHookStack
      (hookStack - decodeErrorHookStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - decodeErrorHookStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeErrorPushBudgetSpec M A lim).pre (d, e, n, st) s0 ∗ R' := by
    dsimp only [decodeErrorPushBudgetSpecWithStack, decodeErrorPushBudgetSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (d, e, n, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeErrorPushBudgetSpecWithStack, decodeErrorPushBudgetSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [decodeErrorPushBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [decodeErrorPushBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeErrorPushBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem decodeVarintSlowWithStack_of_decodeVarintSlow {M : AllocCostModel}
    {P : Program} {addr : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {hookStack : Nat}
    (h : subroutine_ok P addr (decodeVarintSlowBudgetSpec M A lim))
    (hle : varintSlowStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (decodeVarintSlowBudgetSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨slotA, slot, ptr, bs, st⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗
        stackAt s0.sp varintSlowStack := by
    have h1 := stackAt_split_bottom s0.sp varintSlowStack
      (hookStack - varintSlowStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - varintSlowStack) ∗ R
  have hpre' : s0.mem ⊨ (decodeVarintSlowBudgetSpec M A lim).pre (slotA, slot, ptr, bs, st) s0 ∗ R' := by
    dsimp only [decodeVarintSlowBudgetSpecWithStack, decodeVarintSlowBudgetSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (slotA, slot, ptr, bs, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [decodeVarintSlowBudgetSpecWithStack, decodeVarintSlowBudgetSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [decodeVarintSlowBudgetSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan
    exact False.elim hpan.1
  · dsimp only [decodeVarintSlowBudgetSpec] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · dsimp only [decodeVarintSlowBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

/-! ## `VmPreserved`-strengthened `black_box`, `Uuid::try_parse`, and `rng_fill` specs -/

def blackBoxU8BudgetSpec : Spec (BitVec 64) :=
  withVmPreserved CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec

abbrev blackBoxU8Spec : Spec (BitVec 64) := blackBoxU8BudgetSpec

theorem blackBoxU8_of_blackBox {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (withVmPreserved blackBoxSpec)) :
    subroutine_ok P addr blackBoxU8BudgetSpec := by
  refine subroutine_ok_outcome_intro fun v R s0 hpc hrun hpre hal =>
    h.mono_outcome v R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [withVmPreserved, blackBoxSpec, blackBoxU8BudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.blackBoxU8Spec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0, htr⟩, hR⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = v.setWidth 8 := by
      rw [hx0]
      change ((v.setWidth 8).setWidth 64).setWidth 8 = v.setWidth 8
      rw [BitVec.setWidth_setWidth_of_le (v.setWidth 8) (by decide : 8 ≤ 64), BitVec.setWidth_eq]
    exact ⟨hvm, ⟨h8, htr⟩, hR⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def uuidTryParseAnyBudgetSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnySpec

abbrev uuidTryParseAnySpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) :=
  uuidTryParseAnyBudgetSpec

theorem uuidTryParseAny_of_spec {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (uuidTryParseBudgetSpec uuidTryParse)) :
    subroutine_ok P addr uuidTryParseAnyBudgetSpec := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal =>
    h.mono_outcome (p, bs, out) R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [uuidTryParseBudgetSpec, uuidTryParseAnyBudgetSpec, withVmPreserved,
      uuidTryParseSpec, CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnySpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hmem⟩
    refine ⟨hvm, htr, ?_⟩
    exact Satisfies.mono
      (sepConj_mono_right (sepConj_mono_left (uuidResultAt_entails_any out (uuidTryParse bs)))) hmem
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem uuidTryParseAnyWithStack_of_code {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (h : subroutine_ok P addr (uuidTryParseCodeBudgetSpec uuidTryParse))
    (hle : uuidTryParseStack ≤ hookStack := by decide)
    (hmax : hookStack ≤ 2 ^ 64 := by decide) :
    subroutine_ok P addr (withStack uuidTryParseAnyBudgetSpec hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨p, bs, out⟩ R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
        stackAt s0.sp uuidTryParseStack := by
    have h1 := stackAt_split_bottom s0.sp uuidTryParseStack
      (hookStack - uuidTryParseStack) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R
  have hpre' : s0.mem ⊨ (uuidTryParseCodeBudgetSpec uuidTryParse).pre (p, bs, out) s0 ∗ R' := by
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      uuidTryParseAnyBudgetSpec, uuidTryParseCodeBudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnySpec,
      uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome (p, bs, out) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan_sat⟩ | ⟨code, _, hex_sat⟩ | ⟨_, hoom_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [uuidTryParseCodeBudgetSpec, withVmPreserved,
      uuidTryParseCodeSpec, uuidTryParseSpec, R'] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hvm, hpost_mem⟩
    have hpost' : sf.mem ⊨
        (((⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗
            CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnyResultAt out) ∗
          stackAt s0.sp uuidTryParseStack) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R)) := by
      have h1 : sf.mem ⊨
          ((⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗ uuidResultAt out (uuidTryParse bs)) ∗
            stackAt s0.sp uuidTryParseStack) ∗
          (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗ R) := by
        ac_nf at hpost_mem ⊢
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_right
        (sepConj_mono_right (uuidResultAt_entails_any out (uuidTryParse bs)))))) h1
    dsimp only [withStack, CryptoVerification.LibsignalTripleRatchet.withStack,
      uuidTryParseAnyBudgetSpec, withVmPreserved,
      CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnySpec]
    rw [hsplit]
    have hgoal : sf.mem ⊨
        ⌜VmPreserved s0 sf⌝ ∗
          (((⌜sf.trace = s0.trace⌝ ∗ (p ↦ₛ bs) ∗
              CryptoVerification.LibsignalTripleRatchet.uuidTryParseAnyResultAt out) ∗
            (memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - uuidTryParseStack) ∗
              stackAt s0.sp uuidTryParseStack)) ∗ R) := by
      rw [satisfies_pure_sepConj]
      refine ⟨hvm, ?_⟩
      ac_nf at hpost' ⊢
    ac_nf at hgoal ⊢
  · have h0 : (uuidTryParseCodeBudgetSpec uuidTryParse).onPanic (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hpan_sat
    exact False.elim hpan_sat.1
  · have h0 : (uuidTryParseCodeBudgetSpec uuidTryParse).onExit (p, bs, out) code s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hex_sat
    exact False.elim hex_sat.1
  · have h0 : (uuidTryParseCodeBudgetSpec uuidTryParse).onOom (p, bs, out) s0 sf = ⌜False⌝ := rfl
    rw [h0, satisfies_pure_sepConj] at hoom_sat
    exact False.elim hoom_sat.1

def rngFillAnyBudgetSpec : Spec (BitVec 64 × Nat) :=
  withVmPreserved CryptoVerification.LibsignalTripleRatchet.rngFillAnySpec

abbrev rngFillAnySpec : Spec (BitVec 64 × Nat) := rngFillAnyBudgetSpec

/-! ## AES-256-CBC and empty-state `spqr::recv` budget specs -/

abbrev aesEncFnSpec := @aesEncFnBudgetSpec
abbrev aesDecFnSpec := @aesDecFnBudgetSpec
abbrev aesDecWeakSpec := @aesDecWeakBudgetSpec

theorem aesDecWeak_of_aesDec {M : AllocCostModel} {P : Program} {addr : BitVec 64}
    {D : AesKey → Block → Block} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (aesDecBudgetSpec D M A lim)) :
    subroutine_ok P addr (aesDecWeakBudgetSpec D M A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hal =>
    h.mono_outcome (x, st) R s0 hpc hrun hpre hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [aesDecBudgetSpec, aesDecWeakBudgetSpec, aesDecFnBudgetSpec,
      sepConj_assoc, sepExists_sepConj_left, satisfies_sepExists,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨evs, hpure, hmem_post⟩
    refine ⟨evs, hpure, ?_⟩
    cases hdec : aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
    | some pt =>
      simpa only [hdec, sepConj_assoc] using hmem_post
    | none =>
      simp only [hdec, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists] at hmem_post ⊢
      rcases hmem_post with ⟨p, hmem_p⟩
      have h1 : sf.mem ⊨ ⌜p ≠ 0⌝ ∗ (x.frame ∗ (x.ret ↦₆₄ errTag) ∗
          (((x.ret + 8#64) ↦₆₄ p) ∗ memRegion (x.ret + 16#64) 8) ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack ∗ R) := by
        ac_nf at hmem_p ⊢
      rw [satisfies_pure_sepConj] at h1
      rcases h1 with ⟨_, hrest⟩
      rw [memRegion_split' (b := x.ret + 8#64) (b' := x.ret + 16#64) (n := 8) (k := 8)
        (by decide) (by bv_omega) (by decide), memRegion_eight]
      simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
        satisfies_sepExists]
      exact ⟨p, by ac_nf at hrest ⊢⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Relational empty-state `spqr::recv` budget contract (`st.bytes = []` in `pre` at `spqrRecvStack`),
parameterized by allocator event envelope `Env : List (BitVec 8) → List AllocEvent → Prop`
(`onPanic = ⌜False⌝` under `FitsEnv M lim s (Env msg.bytes)`). -/
def spqrRecvEmptyAnyBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : List (BitVec 8) → List AllocEvent → Prop) :
    Spec (VecArg × VecArg × BitVec 64 × M.σ) where
  pre := fun (st, msg, ret, s_m) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret ∧
      st.bytes = [] ∧ FitsEnv M lim s_m (Env msg.bytes)⌝ ∗
      st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim s_m s ∗ stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret, s_m) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      (∃∗ res : Except Bool (List (BitVec 8) × Salt),
        ⌜res = .ok ([], none) ∨ (msg.bytes ≠ [] ∧ ∃ sd, res = .error sd)⌝ ∗
          spqrRecvResultAt A.repAlloc ret res) ∗
      (∃∗ evs : List AllocEvent, ⌜Env msg.bytes evs⌝ ∗
        A.pool lim (M.stepEvents evs s_m) sf) ∗
      stackAt s0.sp spqrRecvStack

abbrev spqrRecvEmptyAnySpec := @spqrRecvEmptyAnyBudgetSpec

end LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
