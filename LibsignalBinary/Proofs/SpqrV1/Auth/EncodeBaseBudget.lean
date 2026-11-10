/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.AuthEncodeMergeCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBase
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Specifications and Event Transitions for `Authenticator::encode`

Defines deterministic allocator event transitions (`reserveStep`, `pushBytesStep`,
`optBytesField1ByteTagStep`, `authEncodeStep`, `authEncodeEvents`, `AuthEncodeEnv`),
exact-fit `0`-allocation lemmas, and budget-threaded contracts (`authEncodePinnedSpecOfEnv`,
`authEncodeSpecOfEnv`, `authEncodeExactSpecOf`) for `encode<Authenticator> [local#1, 2]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   rustAllocEvents rustReallocEvents)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks lsmpl withLsCodeLoaded blkPl_151 blkPl_314 lsProg_151 lsProg_314)
open CryptoVerification.RustHeap (RustAlloc vecU8At vecHeader)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (AuthenticatorPB)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeBytesField)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall reserveCap doReserveStack doReserveStackX sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (vecU8Buf vecU8At_eq_header_sep_buf StepInvPlaced)
open CryptoVerification.SpqrV1.ProtoRepr
  (authenticatorPBAt authenticatorPBEncodedLen authenticatorPBPinnedAt)
open CryptoVerification.SpqrV1.Auth
  (AuthEncodeGhost AuthEncodePinnedGhost AuthEncodeCalleeSaved withAuthEncodeCS
   authEncodeStackOf bytesField_1_length_of_ne_nil bytesField_2_length_of_ne_nil
   encodeAuthMsg encodeAuthMsg_length sp_sub_64_aligned)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents)

/-! ## Deterministic Allocator Event Transitions -/

/-- Deterministic `(newCap, evs)` transition for `Vec<u8>` capacity reservation. -/
def reserveStep (cap len additional : Nat) : Nat × List AllocEvent :=
  if len + additional ≤ cap then
    (cap, [])
  else
    let newCap := reserveCap cap len additional
    let evs := if cap = 0 then rustAllocEvents newCap 1 else rustReallocEvents cap newCap 1
    (newCap, evs)

theorem reserveStep_one_eq_pushByteStep (cap len : Nat) :
    reserveStep cap len 1 = pushByteStep cap len := by
  unfold reserveStep pushByteStep
  by_cases h : len < cap
  · have hle : len + 1 ≤ cap := h
    simp only [h, hle, ↓reduceIte]
  · have hnle : ¬ (len + 1 ≤ cap) := h
    simp only [h, hnle, ↓reduceIte]

theorem reserveStep_of_spare {cap len additional : Nat} (h : len + additional ≤ cap) :
    reserveStep cap len additional = (cap, []) := by
  simp only [reserveStep, h, ↓reduceIte]

theorem reserveStep_of_need {cap len additional : Nat} (h : ¬ (len + additional ≤ cap)) :
    reserveStep cap len additional =
      (reserveCap cap len additional,
       if cap = 0 then rustAllocEvents (reserveCap cap len additional) 1
       else rustReallocEvents cap (reserveCap cap len additional) 1) := by
  simp only [reserveStep, h, ↓reduceIte]

theorem reserveStep_of_need_doReserveEvents (v curCap curPtr : BitVec 64)
    (curBs : List (BitVec 8)) (additional : Nat)
    (h : ¬ (curBs.length + additional ≤ curCap.toNat)) :
    reserveStep curCap.toNat curBs.length additional =
      (reserveCap curCap.toNat curBs.length additional,
       doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) := by
  rw [reserveStep_of_need h]
  unfold doReserveEvents
  congr 1
  by_cases h0 : curCap = 0#64
  · rw [h0]; rfl
  · have h0n : curCap.toNat ≠ 0 := fun h0n => h0 (BitVec.eq_of_toNat_eq h0n)
    simp only [h0, h0n, ↓reduceIte]

theorem reserveStep_fst_ge (cap len additional : Nat) :
    cap ≤ (reserveStep cap len additional).1 := by
  unfold reserveStep
  split_ifs with h h0 <;> simp only [reserveCap] <;> omega

/-- Capacity-and-events transition for pushing `n` bytes one-by-one into `Vec<u8>`. -/
def pushBytesStep : Nat → Nat → Nat → Nat × List AllocEvent
  | 0, cap, _ => (cap, [])
  | n + 1, cap, len =>
    let s1 := pushByteStep cap len
    let s2 := pushBytesStep n s1.1 (len + 1)
    (s2.1, s1.2 ++ s2.2)

theorem pushBytesStep_snd_eq :
    ∀ (n cap len : Nat), (pushBytesStep n cap len).2 = pushBytesEvents n cap len
  | 0, _, _ => rfl
  | n + 1, cap, len => by
    simp only [pushBytesStep, pushBytesEvents, pushBytesStep_snd_eq n]

theorem pushBytesStep_of_spare :
    ∀ (n cap len : Nat), len + n ≤ cap → pushBytesStep n cap len = (cap, [])
  | 0, _, _, _ => rfl
  | n + 1, cap, len, h => by
    have hlt : len < cap := by omega
    simp only [pushBytesStep, pushByteStep, hlt, ↓reduceIte, List.nil_append]
    exact pushBytesStep_of_spare n cap (len + 1) (by omega)

theorem pushBytesStep_fst_ge :
    ∀ (n cap len : Nat), cap ≤ (pushBytesStep n cap len).1
  | 0, _, _ => Nat.le_refl _
  | n + 1, cap, len => by
    have h1 : cap ≤ (pushByteStep cap len).1 := by
      unfold pushByteStep
      split_ifs with hlt <;> simp only [reserveCap] <;> omega
    exact Nat.le_trans h1 (pushBytesStep_fst_ge n (pushByteStep cap len).1 (len + 1))

/-- Capacity-and-events transition for an optional `bytes` field with a 1-byte tag. -/
def optBytesField1ByteTagStep (cap len : Nat) (bs : List (BitVec 8)) : Nat × List AllocEvent :=
  if bs.isEmpty then
    (cap, [])
  else
    let vlen := (encodeVarint (BitVec.ofNat 64 bs.length)).length
    let s1 := pushBytesStep (vlen + 1) cap len
    let s2 := reserveStep s1.1 (len + 1 + vlen) bs.length
    (s2.1, s1.2 ++ s2.2)

theorem optBytesField1ByteTagStep_of_spare {cap len : Nat} {bs : List (BitVec 8)}
    {fieldLen : Nat}
    (hne : bs.isEmpty = false →
      fieldLen = 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length + bs.length)
    (h : len + fieldLen ≤ cap) :
    optBytesField1ByteTagStep cap len bs = (cap, []) := by
  unfold optBytesField1ByteTagStep
  cases he : bs.isEmpty
  · have hlen := hne he
    dsimp only [Bool.false_eq_true, ↓reduceIte]
    have hs1 : pushBytesStep ((encodeVarint (BitVec.ofNat 64 bs.length)).length + 1) cap len =
        (cap, []) :=
      pushBytesStep_of_spare _ _ _ (by omega)
    rw [hs1]
    have hs2 : reserveStep cap (len + 1 + (encodeVarint (BitVec.ofNat 64 bs.length)).length)
        bs.length = (cap, []) :=
      reserveStep_of_spare (by omega)
    rw [hs2]
    rfl
  · rfl

/-- Capacity-and-events transition for `Authenticator::encode` (`tag = 2#32`). -/
def authEncodeStep (cap len : Nat) (auth : AuthenticatorPB) : Nat × List AllocEvent :=
  let hdrVlen := (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length
  let s1 := pushBytesStep (hdrVlen + 1) cap len
  let rkLen := (encodeBytesField 1#32 auth.rootKey).length
  let s2 := optBytesField1ByteTagStep s1.1 (len + 1 + hdrVlen) auth.rootKey
  let s3 := optBytesField1ByteTagStep s2.1 (len + 1 + hdrVlen + rkLen) auth.macKey
  (s3.1, s1.2 ++ s2.2 ++ s3.2)

theorem authEncodeStep_of_spare {cap len : Nat} {auth : AuthenticatorPB}
    (h : len + (encodeAuthMsg auth).length ≤ cap) :
    authEncodeStep cap len auth = (cap, []) := by
  rw [encodeAuthMsg_length] at h
  dsimp only [authEncodeStep]
  have hs1 : pushBytesStep
      ((encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length + 1) cap len =
      (cap, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : optBytesField1ByteTagStep cap
      (len + 1 + (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length)
      auth.rootKey = (cap, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (encodeBytesField 1#32 auth.rootKey).length)
      (fun he => bytesField_1_length_of_ne_nil (List.isEmpty_eq_false_iff.mp he))
      (by omega)
  rw [hs2]
  have hs3 : optBytesField1ByteTagStep cap
      (len + 1 + (encodeVarint (BitVec.ofNat 64 (authenticatorPBEncodedLen auth))).length +
        (encodeBytesField 1#32 auth.rootKey).length)
      auth.macKey = (cap, []) :=
    optBytesField1ByteTagStep_of_spare
      (fieldLen := (encodeBytesField 2#32 auth.macKey).length)
      (fun he => bytesField_2_length_of_ne_nil (List.isEmpty_eq_false_iff.mp he))
      (by omega)
  rw [hs3]
  rfl

def authPinnedToUnpinned (x : AuthEncodePinnedGhost) : AuthEncodeGhost :=
  ⟨x.authA, x.auth, x.v, x.cap, x.ptr, x.bs⟩

/-- Deterministic `AllocEvent` list emitted by `Authenticator::encode`. -/
def authEncodeEvents (x : AuthEncodeGhost) : List AllocEvent :=
  (authEncodeStep x.cap.toNat x.bs.length x.auth).2

def AuthEncodeEnv (x : AuthEncodeGhost) (evs : List AllocEvent) : Prop :=
  evs = authEncodeEvents x

theorem authEncodeEnv_events (x : AuthEncodeGhost) :
    AuthEncodeEnv x (authEncodeEvents x) := rfl

theorem authEncodeEvents_of_spare {x : AuthEncodeGhost}
    (h : x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat) :
    authEncodeEvents x = [] := by
  unfold authEncodeEvents
  rw [authEncodeStep_of_spare h]

theorem fitsEnv_authEncode_of_spare {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : AuthEncodeGhost} (h : x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat) :
    FitsEnv M lim st (AuthEncodeEnv x) :=
  FitsEnv.eq_iff.mpr (by rw [authEncodeEvents_of_spare h]; trivial)

theorem authEncodeEnv_eq_nil_of_spare {x : AuthEncodeGhost} {evs : List AllocEvent}
    (h : x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat)
    (hev : AuthEncodeEnv x evs) : evs = [] :=
  hev.trans (authEncodeEvents_of_spare h)

/-! ## Budget-Threaded Specifications -/

/-- Envelope-parameterized pinned budget specification of `Authenticator::encode`. -/
def authEncodePinnedSpecOfEnv (resStack : Nat)
    (Env : AuthEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env (authPinnedToUnpinned x))⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env (authPinnedToUnpinned x) evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Envelope-parameterized unpinned budget specification of `Authenticator::encode`. -/
def authEncodeSpecOfEnv (resStack : Nat)
    (Env : AuthEncodeGhost → List AllocEvent → Prop)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeAuthMsg x.auth).length + 10 < 2 ^ 62) ∧
      FitsEnv M lim st (Env x)⌝ ∗
      authenticatorPBAt A.repAlloc x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBAt A.repAlloc x.authA x.auth ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
            cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
          vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth)) ∗
      (∃∗ evs : List AllocEvent, ⌜Env x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp (authEncodeStackOf resStack)

abbrev authEncodePinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodePinnedGhost × M.σ) :=
  authEncodePinnedSpecOfEnv resStack AuthEncodeEnv A lim

abbrev authEncodeSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodeGhost × M.σ) :=
  authEncodeSpecOfEnv resStack AuthEncodeEnv A lim

abbrev authEncodePinnedSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodePinnedGhost × M.σ) :=
  authEncodePinnedSpecOf doReserveStack A lim

abbrev authEncodePinnedSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodePinnedGhost × M.σ) :=
  authEncodePinnedSpecOf doReserveStackX A lim

abbrev authEncodeSpec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodeGhost × M.σ) :=
  authEncodeSpecOf doReserveStack A lim

abbrev authEncodeSpecX {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodeGhost × M.σ) :=
  authEncodeSpecOf doReserveStackX A lim

/-- Exact-capacity (`0`-allocation) pinned budget specification of `Authenticator::encode`. -/
def authEncodeExactSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodePinnedGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeAuthMsg x.auth) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (authEncodeStackOf resStack)

/-- Exact-capacity (`0`-allocation) unpinned budget specification of `Authenticator::encode`. -/
def authEncodeExactUnpinnedSpecOf (resStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AuthEncodeGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.authA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat⌝ ∗
      authenticatorPBAt A.repAlloc x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st s ∗
      stackAt s.sp (authEncodeStackOf resStack)
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBAt A.repAlloc x.authA x.auth ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeAuthMsg x.auth) ∗
      A.pool lim st sf ∗
      stackAt s0.sp (authEncodeStackOf resStack)

theorem subroutine_ok_authEncodeExact_of_pinned {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (authEncodePinnedSpecOf resStack A lim)) :
    subroutine_ok prog entry (authEncodeExactSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [authEncodeExactSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hpre' : s0.mem ⊨ (authEncodePinnedSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, fitsEnv_authEncode_of_spare hfit⟩, hmem⟩
  refine hok.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [authEncodePinnedSpecOf, authEncodePinnedSpecOfEnv] at hq
    dsimp only [authEncodeExactSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htrf, hq⟩ := hq
    refine ⟨htrf, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨evs, cap', ptr', hq⟩
    have hq' : sf.mem ⊨ ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        (⌜AuthEncodeEnv (authPinnedToUnpinned x) evs⌝ ∗
          (authenticatorPBPinnedAt A.repAlloc x.g x.authA x.auth ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hev, hmem'⟩ := hq'
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hevs_nil := authEncodeEnv_eq_nil_of_spare hfit hev
    subst hevs_nil
    simp only [AllocCostModel.stepEvents_nil] at hmem'
    convert hmem' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

theorem subroutine_ok_authEncodeExactUnpinned_of_unpinned {resStack : Nat} {prog : Program}
    {entry : BitVec 64} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hok : subroutine_ok prog entry (authEncodeSpecOf resStack A lim)) :
    subroutine_ok prog entry (authEncodeExactUnpinnedSpecOf resStack A lim) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [authEncodeExactUnpinnedSpecOf] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hfit⟩, hmem⟩ := hpre
  have hpre' : s0.mem ⊨ (authEncodeSpecOf resStack A lim).pre (x, st) s0 ∗ R := by
    dsimp only [authEncodeSpecOf, authEncodeSpecOfEnv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hfit, fitsEnv_authEncode_of_spare hfit⟩, hmem⟩
  refine hok.mono_outcome (x, st) R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [authEncodeSpecOf, authEncodeSpecOfEnv] at hq
    dsimp only [authEncodeExactUnpinnedSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    obtain ⟨htrf, hq⟩ := hq
    refine ⟨htrf, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨evs, cap', ptr', hq⟩
    have hq' : sf.mem ⊨ ⌜x.cap.toNat ≤ cap'.toNat ∧
        (x.bs.length + (encodeAuthMsg x.auth).length ≤ x.cap.toNat →
          cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        (⌜AuthEncodeEnv x evs⌝ ∗
          (authenticatorPBAt A.repAlloc x.authA x.auth ∗
            vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeAuthMsg x.auth) ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp (authEncodeStackOf resStack) ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hq'
    obtain ⟨⟨_, hpres⟩, hev, hmem'⟩ := hq'
    obtain ⟨rfl, rfl⟩ := hpres hfit
    have hevs_nil := authEncodeEnv_eq_nil_of_spare hfit hev
    subst hevs_nil
    simp only [AllocCostModel.stepEvents_nil] at hmem'
    convert hmem' using 1; sep_ac_rfl
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)

/-! ## Placed Contract Propositions and Call Helpers -/

def AuthEncode1PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpec A lim))

def AuthEncode1PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base
    (withLsCodeLoaded lsmpl (authEncodeSpec A lim))

def AuthEncode1PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpecX A lim))

def AuthEncode1PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_151 H) (blkPl_151).base
    (withLsCodeLoaded lsmpl (authEncodeSpecX A lim))

def AuthEncode2PinnedPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_314 H) (blkPl_314).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpec A lim))

def AuthEncode2PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_314 H) (blkPl_314).base
    (withLsCodeLoaded lsmpl (authEncodeSpec A lim))

def AuthEncode2PinnedPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_314 H) (blkPl_314).base
    (withLsCodeLoaded lsmpl (authEncodePinnedSpecX A lim))

def AuthEncode2PlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_314 H) (blkPl_314).base
    (withLsCodeLoaded lsmpl (authEncodeSpecX A lim))

/-- Polymorphic-outcome pure-bounds extraction for `vecU8At`. -/
theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hhm : s.mem ⊨ vecU8Buf A cap ptr bs ∗ (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ F ∗ R) := by
    rw [hP, vecU8At_eq_header_sep_buf] at hm
    convert hm using 1; sep_ac_rfl
  unfold vecU8Buf at hhm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

/-- Executes `sessionMemcpyRegionBudgetSpec` at `s.sp = sp - 64#64`, propagating `VmPreserved` and `StepInvPlaced`. -/
theorem step_auth_memcpy_call_placed {prog : Program} {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionBudgetSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {ret : BitVec 64} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → StepInvPlaced s sm → VmPreserved s sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  intro R hm hL
  have hpre : s.mem ⊨ sessionMemcpyRegionBudgetSpec.pre (dst, src, bs) s ∗ (F ∗ R) := by
    rw [hP] at hm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by convert hm using 1; sep_ac_rfl⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hmemcpy.no_fault_before_outcome (dst, src, bs) (F ∗ R) s hpc hrun hpre hsp_aligned hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpan_mem⟩ | ⟨_, _, hex_mem⟩ | ⟨_, hoom_mem⟩
  · rw [hlr] at hpcm; rw [hsp] at hspm
    simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨hvm, ⟨_, htrm⟩, hmem_post⟩ := hpost
    have hmem_post' : sm.mem ⊨ (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F) ∗ R := by
      convert hmem_post using 1; sep_ac_rfl
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (StepInvPlaced.of_steps hsteps) hvm R
        hmem_post' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · simp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec,
      satisfies_pure_sepConj] at hpan_mem
    exact hpan_mem.1.elim
  · exact (allowPanic_not_exited hex_mem).elim
  · exact (not_satisfies_false_sepConj hoom_mem).elim

end LibsignalBinary.Proofs.SpqrV1.Auth.EncodeBaseBudget
