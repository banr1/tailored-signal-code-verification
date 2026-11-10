/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCS
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Shared Base for `prost::encoding::message::encode::<ChainParams, Vec<u8>>`

Defines the multi-step `Vec<u8>` growth event-chain relation `VecU8ReserveChain` and envelope
`VecU8EncodeEnv`, together with envelope-parameterized, concrete, and exact-capacity (`VmPreserved`)
specifications for `encode<ChainParams>` (`[local#1, 2]`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustAllocEvents rustReallocEvents)
open CryptoVerification.RustHeap (RustAlloc vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStack doReserveStackX tripleRatchetProgAtExt)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodeChainParamsGhost encodeChainParams1Name encodeChainParams2Name
   encodeChainParamsMsg msgEnc48VarintStackOf)

/-! ## 1. Composable `Vec<u8>` Growth Event Chain (`VecU8ReserveChain` / `VecU8EncodeEnv`) -/

/-- Amortized `RawVec<u8>::reserve::do_reserve_and_handle` target capacity (`stride = 1`):
`max (max (len + additional) (2 * cap)) 8`. -/
abbrev vecU8ReserveCap (cap len additional : Nat) : Nat :=
  max (max (len + additional) (2 * cap)) 8

/-- Multi-step `Vec<u8>` growth event chain from initial capacity `cap0` to final capacity `capOut`
while encoding up to `finalLen` total bytes:
- When `finalLen ≤ cap0`, only `.nil` applies (`capOut = cap0` and `evs = []`).
- Each growth step (`cap0 < finalLen`) advances `cap0 < cap1 ≤ max (max finalLen (2 * cap0)) 8`
  and emits `rustAllocEvents cap1 1` (`cap0 = 0`) or `rustReallocEvents cap0 cap1 1` (`cap0 ≠ 0`).
  This uniformly covers both `<RawVec<u8>>::grow_one` (`additional = 1`) and
  `RawVecInner::reserve::do_reserve_and_handle` (`curLen + additional ≤ finalLen`). -/
inductive VecU8ReserveChain : Nat → Nat → Nat → List AllocEvent → Prop where
  | nil (cap finalLen : Nat) : VecU8ReserveChain cap cap finalLen []
  | grow {cap0 cap1 capOut finalLen : Nat} {evs : List AllocEvent} :
      cap0 < finalLen →
      cap0 < cap1 →
      cap1 ≤ max (max finalLen (2 * cap0)) 8 →
      VecU8ReserveChain cap1 capOut finalLen evs →
      VecU8ReserveChain cap0 capOut finalLen
        ((if cap0 = 0 then rustAllocEvents cap1 1 else rustReallocEvents cap0 cap1 1) ++ evs)

theorem VecU8ReserveChain.cap_le {cap0 capOut finalLen : Nat} {evs : List AllocEvent}
    (h : VecU8ReserveChain cap0 capOut finalLen evs) : cap0 ≤ capOut := by
  induction h with
  | nil => exact Nat.le_refl _
  | grow _ hlt _ _ ih => omega

theorem VecU8ReserveChain.eq_nil_of_le {cap0 capOut finalLen : Nat} {evs : List AllocEvent}
    (hle : finalLen ≤ cap0) (h : VecU8ReserveChain cap0 capOut finalLen evs) :
    capOut = cap0 ∧ evs = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | grow hlt => omega

theorem VecU8ReserveChain.mono_finalLen {cap0 capOut len1 len2 : Nat} {evs : List AllocEvent}
    (hle : len1 ≤ len2) (h : VecU8ReserveChain cap0 capOut len1 evs) :
    VecU8ReserveChain cap0 capOut len2 evs := by
  induction h with
  | nil cap _ => exact .nil cap len2
  | grow hlt0 hlt1 hbnd _ ih =>
    exact .grow (by omega) hlt1 (by omega) (ih hle)

theorem VecU8ReserveChain.trans {c0 c1 c2 len1 len2 : Nat} {evs1 evs2 : List AllocEvent}
    (hle : len1 ≤ len2)
    (h1 : VecU8ReserveChain c0 c1 len1 evs1)
    (h2 : VecU8ReserveChain c1 c2 len2 evs2) :
    VecU8ReserveChain c0 c2 len2 (evs1 ++ evs2) := by
  induction h1 with
  | nil =>
    simp only [List.nil_append]
    exact h2
  | grow hlt0 hlt1 hbnd _ ih =>
    rw [List.append_assoc]
    exact .grow (by omega) hlt1 (by omega) (ih hle h2)

theorem VecU8ReserveChain.single_reserve {cap0 curLen additional finalLen : Nat}
    (hneed : cap0 < curLen + additional)
    (hle : curLen + additional ≤ finalLen) :
    VecU8ReserveChain cap0 (vecU8ReserveCap cap0 curLen additional) finalLen
      (if cap0 = 0 then rustAllocEvents (vecU8ReserveCap cap0 curLen additional) 1
       else rustReallocEvents cap0 (vecU8ReserveCap cap0 curLen additional) 1) := by
  have heq :
      (if cap0 = 0 then rustAllocEvents (vecU8ReserveCap cap0 curLen additional) 1
       else rustReallocEvents cap0 (vecU8ReserveCap cap0 curLen additional) 1) =
      (if cap0 = 0 then rustAllocEvents (vecU8ReserveCap cap0 curLen additional) 1
       else rustReallocEvents cap0 (vecU8ReserveCap cap0 curLen additional) 1) ++ [] := by
    rw [List.append_nil]
  rw [heq]
  exact .grow (by omega) (by dsimp [vecU8ReserveCap]; omega)
    (by dsimp [vecU8ReserveCap]; omega) (.nil _ _)

/-- Allocator event envelope for appending up to `finalLen - bs.length` bytes into a `Vec<u8>`
with initial capacity `cap0`. -/
def VecU8EncodeEnv (cap0 finalLen : Nat) (evs : List AllocEvent) : Prop :=
  ∃ capOut, VecU8ReserveChain cap0 capOut finalLen evs

theorem VecU8EncodeEnv.nil (cap0 finalLen : Nat) : VecU8EncodeEnv cap0 finalLen [] :=
  ⟨cap0, .nil cap0 finalLen⟩

theorem VecU8EncodeEnv.eq_nil_of_le {cap0 finalLen : Nat} {evs : List AllocEvent}
    (hle : finalLen ≤ cap0) (h : VecU8EncodeEnv cap0 finalLen evs) : evs = [] := by
  rcases h with ⟨_, hc⟩
  exact (hc.eq_nil_of_le hle).2

theorem VecU8EncodeEnv.mono_finalLen {cap0 len1 len2 : Nat} {evs : List AllocEvent}
    (hle : len1 ≤ len2) (h : VecU8EncodeEnv cap0 len1 evs) : VecU8EncodeEnv cap0 len2 evs := by
  rcases h with ⟨capOut, hc⟩
  exact ⟨capOut, hc.mono_finalLen hle⟩

theorem fitsEnv_vecU8EncodeEnv_of_spare (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    {cap0 finalLen : Nat} (hle : finalLen ≤ cap0) :
    FitsEnv M lim st (VecU8EncodeEnv cap0 finalLen) := by
  intro evs hev
  rw [hev.eq_nil_of_le hle]
  trivial

/-! ## 2. Budget-Threaded Specifications of `encode<ChainParams>` (`[local#1, 2]`) -/

/-- Concrete allocator event envelope of `prost::encoding::message::encode::<ChainParams, Vec<u8>>`. -/
def EncodeChainParamsEnv (x : EncodeChainParamsGhost) (evs : List AllocEvent) : Prop :=
  VecU8EncodeEnv x.cap.toNat (x.bs.length + (encodeChainParamsMsg x.tag x.p).length) evs

theorem encodeChainParamsEnv_eq_nil_of_spare {x : EncodeChainParamsGhost} {evs : List AllocEvent}
    (hle : x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat)
    (h : EncodeChainParamsEnv x evs) : evs = [] :=
  VecU8EncodeEnv.eq_nil_of_le hle h

/-- Envelope-parameterized budget specification of
`prost::encoding::message::encode::<ChainParams, Vec<u8>>` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodeChainParamsSpecOfEnv (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv : EncodeChainParamsGhost → (List AllocEvent → Prop) → Prop)
    (PostEnv : EncodeChainParamsGhost → List AllocEvent → Prop) :
    Spec (EncodeChainParamsGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length + 10 < 2 ^ 62) ∧
      (∀ Env, PreEnv x Env → FitsEnv M lim st Env)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48VarintStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜PostEnv x evs ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48VarintStackOf resStack)

/-- Concrete budget specification of `prost::encoding::message::encode::<ChainParams, Vec<u8>>`
instantiated with `EncodeChainParamsEnv`. -/
def encodeChainParamsSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeChainParamsGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (EncodeChainParamsEnv x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (msgEnc48VarintStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p)) ∗
      (∃∗ evs : List AllocEvent,
        ⌜EncodeChainParamsEnv x evs ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (msgEnc48VarintStackOf resStack)

/-- Exact-capacity 0-allocation (`VmPreserved`) contract of `encode<ChainParams>` (`A.live`-only,
no `A.pool` required since `x.bs.length + msgLen ≤ x.cap.toNat` skips all allocator calls). -/
def encodeChainParamsExactVmSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodeChainParamsGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s.sp (msgEnc48VarintStackOf resStack)
  post := fun x s0 sf =>
    ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
      stackAt s0.sp (msgEnc48VarintStackOf resStack)

abbrev encodeChainParamsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeChainParamsGhost × M.σ) :=
  encodeChainParamsSpecOf doReserveStack A lim

abbrev encodeChainParamsSpecX {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (EncodeChainParamsGhost × M.σ) :=
  encodeChainParamsSpecOf doReserveStackX A lim

theorem subroutine_ok_encodeChainParams_of_env {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry
      (encodeChainParamsSpecOfEnv resStack A lim
        (fun x Env => Env = EncodeChainParamsEnv x) EncodeChainParamsEnv)) :
    subroutine_ok prog entry (encodeChainParamsSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeChainParamsSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, hfit, hEnv⟩, hrest⟩
  have hpreE : s0.mem ⊨
      (encodeChainParamsSpecOfEnv resStack A lim
        (fun x Env => Env = EncodeChainParamsEnv x) EncodeChainParamsEnv).pre (x, st) s0 ∗ R := by
    dsimp only [encodeChainParamsSpecOfEnv]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, hfit, fun _ h => h ▸ hEnv⟩, hrest⟩
  exact h.mono_outcome (x, st) R s0 hpc hrun hpreE hsp fun _ hout => hout

/-- Derive `encodeChainParamsExactVmSpecOf` (with `A.pool lim st s` in frame) from
`encodeChainParamsSpecOf` on spare-capacity inputs. -/
theorem subroutine_ok_encodeChainParamsExact_of_budget {resStack : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (st : M.σ)
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (encodeChainParamsSpecOf resStack A lim)) :
    subroutine_ok prog entry
      { pre := fun x s => (encodeChainParamsExactVmSpecOf resStack A.repAlloc).pre x s ∗ A.pool lim st s
        post := fun x s0 sf =>
          (encodeChainParamsExactVmSpecOf resStack A.repAlloc).post x s0 sf ∗ A.pool lim st sf } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [encodeChainParamsExactVmSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, hle⟩, hrest⟩
  have hEnv : FitsEnv M lim st (EncodeChainParamsEnv x) :=
    fitsEnv_vecU8EncodeEnv_of_spare M lim st hle
  have hpreB : s0.mem ⊨ (encodeChainParamsSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [encodeChainParamsSpecOf]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, Or.inl hle, hEnv⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hrest
  refine h.mono_outcome (x, st) R s0 hpc hrun hpreB hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeChainParamsSpecOf] at hq
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨evs, cap', ptr', hq⟩
    have hq_reord : sf.mem ⊨
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        (⌜EncodeChainParamsEnv x evs ∧
          (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
            evs = [] ∧ VmPreserved s0 sf)⌝ ∗
        (vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
         A.pool lim (M.stepEvents evs st) sf ∗
         stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq
    rw [satisfies_pure_sepConj] at hq_reord
    rcases hq_reord with ⟨⟨_, hcp⟩, hq_reord⟩
    rw [satisfies_pure_sepConj] at hq_reord
    rcases hq_reord with ⟨⟨_, hev⟩, hq_mem⟩
    rcases hcp hle with ⟨rfl, rfl⟩
    rcases hev hle with ⟨rfl, hvm⟩
    simp only [AllocCostModel.stepEvents] at hq_mem
    dsimp only [encodeChainParamsExactVmSpecOf]
    have hgoal : sf.mem ⊨
        ⌜VmPreserved s0 sf ∧ sf.trace = s0.trace⌝ ∗
        (vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
         A.pool lim st sf ∗
         stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨⟨hvm, htr⟩, hq_mem⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hgoal
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

def EncodeChainParams1OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeChainParams1Name)
    (encodeChainParamsSpec A lim)

def EncodeChainParams1OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeChainParams1Name)
    ((encodeChainParamsSpecX A lim).inImage img)

def EncodeChainParams2OkExt {M : AllocCostModel} (b : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr encodeChainParams2Name)
    (encodeChainParamsSpec A lim)

def EncodeChainParams2OkX {M : AllocCostModel} (img : Obj.Image)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr encodeChainParams2Name)
    ((encodeChainParamsSpecX A lim).inImage img)

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
