/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `SessionStructure::clone` Symbolic Fine-Credit and `sc = 63` Free Cancellation

Proves symbolic `(M : AllocCostModel) [HasFineReallocCredit M]` `PhaseCreditSpec` and
`DeallocCreditSpec` bounds in binary call order for:
1. `optLargeCost M req`: regime-uniform `sc = 63` byte cost (`0` when `req ≤ smallMaxReq M`,
   `largeCost M req` when `smallMaxReq M < req`), pairing `PhaseCreditSpec.rustAlloc_optLarge` with
   `DeallocCreditSpec.free_optLarge`.
2. `vecCloneEvents`, `optTailCloneEvents`, `senderChainCloneEvents`, `chainCloneEvents`, and
   `segCloneEvents G st` (`SegCloneEnv G st`), plus tight per-size-class `cumSmall` refinements.
3. Exact-order `drop_glue<SessionStructure>` deallocation credit (`dropClonedSessionEvents`)
   cancelling every `sc = 63` clone buffer back to `Δlive = 0`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit

open CryptoGames.LibsignalSession (SessionState SenderChain ReceiverChain MessageKeyGenerator)
open CryptoVerification.LibsignalSessionRepr (VecGhost ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  TailVecGhost SenderChainGhost SessionGhost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  ChainCloneEnv SenderChainCloneEnv
  senderChainAsProtoGhost senderChainCloneEvents chainCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  vecCloneEvents optTailCloneEvents segCloneEvents SegCloneEnv
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ModelHyps PhaseCreditSpec DeallocCreditSpec
  ConcatEnv IterConcatEnv iterPeak
)

/-! ## 1. Regime-Uniform `optLargeCost` & Monotone Allocation Combinators -/

/-- Exact `sc = 63` `liveLarge` contribution of a `req`-byte Rust allocation:
`0` when `req ≤ smallMaxReq M` (including `req = 0`), and `largeCost M req` when
`smallMaxReq M < req`. -/
def optLargeCost (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M req

theorem optLargeCost_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    optLargeCost M 0 = 0 := by
  simp [optLargeCost]

theorem optLargeCost_of_le (M : AllocCostModel) [HasFineReallocCredit M] {req : Nat}
    (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    optLargeCost M req = 0 := by
  simp [optLargeCost, hle]

theorem optLargeCost_of_gt (M : AllocCostModel) [HasFineReallocCredit M] {req : Nat}
    (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    optLargeCost M req = HasFineReallocCredit.largeCost M req := by
  simp [optLargeCost, Nat.not_le.mpr hgt]

theorem optLargeCost_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    optLargeCost M req ≤ if req ≤ HasFineReallocCredit.smallMaxReq M then 0 else req + 8195 := by
  unfold optLargeCost
  split
  · exact Nat.le_refl 0
  · rename_i hnot
    exact hM.largeCost_le (Nat.lt_of_not_ge hnot)

theorem optLargeCost_le_add {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    optLargeCost M req ≤ if req = 0 then 0 else req + 8195 := by
  unfold optLargeCost
  split
  · exact Nat.zero_le _
  · rename_i hnot
    have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hnot
    have hne : req ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    exact hM.largeCost_le hgt

/-- Regime-uniform `PhaseCreditSpec` for `rustAllocEvents req al` (`al ≤ 16`) charging exact
`optLargeCost M req` to `Δlive` and `Δpeak`. -/
theorem PhaseCreditSpec.rustAlloc_optLarge {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (2 * req + 9539) (optLargeCost M req) (optLargeCost M req) req := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · rw [optLargeCost_of_le M hle]
    exact (PhaseCreditSpec.rustAlloc_small_any hM hal hle).mono
      (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    rw [optLargeCost_of_gt M hgt]
    have hm := hM.meta_le
    exact (PhaseCreditSpec.rustAlloc_large M hal hgt).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl req)

/-- Regime-uniform `DeallocCreditSpec` for `rustDeallocEvents req al` (`al ≤ 16`) crediting back
exact `optLargeCost M req` from `liveLarge` in both `small` and `sc = 63` regimes. -/
theorem DeallocCreditSpec.free_optLarge (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) :
    DeallocCreditSpec M (· = rustDeallocEvents req al) (optLargeCost M req) := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · rw [optLargeCost_of_le M hle]
    exact DeallocCreditSpec.free_small M hal hle
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    rw [optLargeCost_of_gt M hgt]
    exact DeallocCreditSpec.free_large M hal hgt

/-- Conditional `if p then [] else rustAllocEvents req al` allocation bound (`0` when `p`). -/
theorem PhaseCreditSpec.condRustAlloc_optLarge {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {p : Prop} [Decidable p] {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = if p then [] else rustAllocEvents req al)
      (if p then 0 else 2 * req + 9539)
      (if p then 0 else optLargeCost M req)
      (if p then 0 else optLargeCost M req)
      (if p then 0 else req) := by
  split
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.rustAlloc_optLarge hM hal

/-- Conditional `if p then [] else rustDeallocEvents req al` deallocation credit (`0` when `p`). -/
theorem DeallocCreditSpec.condFree_optLarge (M : AllocCostModel) [HasFineReallocCredit M]
    {p : Prop} [Decidable p] {req al : Nat} (hal : al ≤ 16) :
    DeallocCreditSpec M (· = if p then [] else rustDeallocEvents req al)
      (if p then 0 else optLargeCost M req) := by
  split
  · exact DeallocCreditSpec.nil M
  · exact DeallocCreditSpec.free_optLarge M hal

/-- For pure-allocation phases (`Δpeak = Δlive`), `iterPeak l l xs = (xs.map l).sum`. -/
theorem iterPeak_self {α : Type} (l : α → Nat) (xs : List α) :
    iterPeak l l xs = (xs.map l).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [iterPeak, List.map_cons, List.sum_cons, ih]
    omega

/-- Deterministic list concatenation `evs = e₁ ++ e₂` for monotone (`Δpeak = Δlive`) phases. -/
theorem PhaseCreditSpec.append_eq_self {M : AllocCostModel} [HasFineReallocCredit M]
    {e₁ e₂ : List AllocEvent} {c₁ l₁ r₁ c₂ l₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M (· = e₁) c₁ l₁ l₁ r₁)
    (h₂ : PhaseCreditSpec M (· = e₂) c₂ l₂ l₂ r₂) :
    PhaseCreditSpec M (· = e₁ ++ e₂) (c₁ + c₂) (l₁ + l₂) (l₁ + l₂) (max r₁ r₂) := by
  have hc : PhaseCreditSpec M (· = e₁ ++ e₂) (c₁ + c₂) (l₁ + l₂) (max l₁ (l₁ + l₂)) (max r₁ r₂) :=
    (h₁.concat h₂).of_imp fun _ h => by
      subst h
      exact ⟨e₁, e₂, rfl, rfl, rfl⟩
  exact hc.mono (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

/-- Deterministic `flatMap` over `xs : List α` for monotone (`Δpeak = Δlive`) phases. -/
theorem PhaseCreditSpec.flatMap_eq_self {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (f : α → List AllocEvent) (c l r : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (· = f x) (c x) (l x) (l x) (r x)) :
    PhaseCreditSpec M (· = xs.flatMap f)
      (xs.map c).sum (xs.map l).sum (xs.map l).sum ((xs.map r).foldr max 0) := by
  have heq : ∀ ys : List α, IterConcatEnv (fun x evs => evs = f x) ys (ys.flatMap f) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      exact ⟨f y, ys.flatMap f, rfl, rfl, ih⟩
  have hiter := PhaseCreditSpec.iterConcat (Step := fun x evs => evs = f x) c l l r xs hstep
  rw [iterPeak_self l xs] at hiter
  exact hiter.of_imp fun _ h => by subst h; exact heq xs

/-- Deterministic list concatenation `evs = e₁ ++ e₂` for `DeallocCreditSpec`. -/
theorem DeallocCreditSpec.append_eq {M : AllocCostModel} [HasFineReallocCredit M]
    {e₁ e₂ : List AllocEvent} {c₁ c₂ : Nat}
    (h₁ : DeallocCreditSpec M (· = e₁) c₁)
    (h₂ : DeallocCreditSpec M (· = e₂) c₂) :
    DeallocCreditSpec M (· = e₁ ++ e₂) (c₁ + c₂) :=
  (h₁.concat h₂).of_imp fun _ h => by
    subst h
    exact ⟨e₁, e₂, rfl, rfl, rfl⟩

/-- Deterministic `flatMap` over `xs : List α` for `DeallocCreditSpec`. -/
theorem DeallocCreditSpec.flatMap_eq {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (f : α → List AllocEvent) (c : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, DeallocCreditSpec M (· = f x) (c x)) :
    DeallocCreditSpec M (· = xs.flatMap f) (xs.map c).sum := by
  have heq : ∀ ys : List α, IterConcatEnv (fun x evs => evs = f x) ys (ys.flatMap f) := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      exact ⟨f y, ys.flatMap f, rfl, rfl, ih⟩
  exact (DeallocCreditSpec.iterConcat (Step := fun x evs => evs = f x) c xs hstep).of_imp
    fun _ h => by subst h; exact heq xs

/-! ## 2. Leaf & Chain Clone Bounds (`vecCloneEvents`, `optTailCloneEvents`, `chainCloneEvents`) -/

def vecCloneCum (len : Nat) : Nat :=
  if len = 0 then 0 else 2 * len + 9539

def vecCloneLarge (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len = 0 then 0 else optLargeCost M len

theorem vecCloneLarge_of_le (M : AllocCostModel) [HasFineReallocCredit M] {len : Nat}
    (hle : len ≤ HasFineReallocCredit.smallMaxReq M) :
    vecCloneLarge M len = 0 := by
  unfold vecCloneLarge
  split
  · rfl
  · exact optLargeCost_of_le M hle

theorem PhaseCreditSpec.vecClone {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (v : VecGhost) :
    PhaseCreditSpec M (· = vecCloneEvents v)
      (vecCloneCum v.bytes.length)
      (vecCloneLarge M v.bytes.length)
      (vecCloneLarge M v.bytes.length)
      v.bytes.length := by
  unfold vecCloneEvents vecCloneCum vecCloneLarge
  exact (PhaseCreditSpec.condRustAlloc_optLarge hM (p := v.bytes.length = 0)
    (req := v.bytes.length) (al := 1) (by decide)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)

def optTailCloneLen : Option TailVecGhost → Nat
  | none => 0
  | some g => g.vec.bytes.length

theorem PhaseCreditSpec.optTailClone {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (o : Option TailVecGhost) :
    PhaseCreditSpec M (· = optTailCloneEvents o)
      (vecCloneCum (optTailCloneLen o))
      (vecCloneLarge M (optTailCloneLen o))
      (vecCloneLarge M (optTailCloneLen o))
      (optTailCloneLen o) := by
  cases o with
  | none =>
    simpa [optTailCloneEvents, optTailCloneLen, vecCloneCum, vecCloneLarge] using
      PhaseCreditSpec.nil M
  | some g =>
    simpa [optTailCloneEvents, optTailCloneLen] using PhaseCreditSpec.vecClone hM g.vec

/-- Cumulative small/metadata bound for `chainCloneEvents gc`. -/
def chainCloneCum (gc : ChainGhost × ReceiverChain) : Nat :=
  vecCloneCum gc.1.srk.bytes.length +
  vecCloneCum gc.1.priv.bytes.length +
  (match gc.2.chainKey with | none => 0 | some _ => 2 * 32 + 9539) +
  (if gc.2.messageKeys = [] then 0
   else (2 * (104 * gc.2.messageKeys.length) + 9539) +
     (gc.2.messageKeys.map fun mkg => 2 * mkg.seed.length + 9539).sum)

/-- Exact `sc = 63` `liveLarge` contribution of `chainCloneEvents gc`. -/
def chainCloneLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (gc : ChainGhost × ReceiverChain) : Nat :=
  vecCloneLarge M gc.1.srk.bytes.length +
  vecCloneLarge M gc.1.priv.bytes.length +
  (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32) +
  (if gc.2.messageKeys = [] then 0
   else optLargeCost M (104 * gc.2.messageKeys.length) +
     (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum)

/-- Per-event `maxReq` bound for `chainCloneEvents gc`. -/
def chainCloneMaxReq (gc : ChainGhost × ReceiverChain) : Nat :=
  max (max (max gc.1.srk.bytes.length gc.1.priv.bytes.length) 32)
    (max (104 * gc.2.messageKeys.length)
      ((gc.2.messageKeys.map fun mkg => mkg.seed.length).foldr max 0))

theorem PhaseCreditSpec.chainClone {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (gc : ChainGhost × ReceiverChain) :
    PhaseCreditSpec M (ChainCloneEnv gc)
      (chainCloneCum gc) (chainCloneLarge M gc) (chainCloneLarge M gc) (chainCloneMaxReq gc) := by
  have hsrk := PhaseCreditSpec.vecClone hM gc.1.srk
  have hpriv := PhaseCreditSpec.vecClone hM gc.1.priv
  have hck : PhaseCreditSpec M
      (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1)
      (match gc.2.chainKey with | none => 0 | some _ => 2 * 32 + 9539)
      (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32)
      (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32)
      32 := by
    cases gc.2.chainKey with
    | none => exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    | some _ => exact PhaseCreditSpec.rustAlloc_optLarge hM (by decide)
  have hmks : PhaseCreditSpec M
      (· = if gc.2.messageKeys = [] then []
           else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
             gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))
      (if gc.2.messageKeys = [] then 0
       else (2 * (104 * gc.2.messageKeys.length) + 9539) +
         (gc.2.messageKeys.map fun mkg => 2 * mkg.seed.length + 9539).sum)
      (if gc.2.messageKeys = [] then 0
       else optLargeCost M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum)
      (if gc.2.messageKeys = [] then 0
       else optLargeCost M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum)
      (max (104 * gc.2.messageKeys.length)
        ((gc.2.messageKeys.map fun mkg => mkg.seed.length).foldr max 0)) := by
    split
    · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    · have hbuf := PhaseCreditSpec.rustAlloc_optLarge hM
        (req := 104 * gc.2.messageKeys.length) (al := 8) (by decide)
      have hseeds := PhaseCreditSpec.flatMap_eq_self
        (fun mkg : MessageKeyGenerator => rustAllocEvents mkg.seed.length 1)
        (fun mkg => 2 * mkg.seed.length + 9539)
        (fun mkg => optLargeCost M mkg.seed.length)
        (fun mkg => mkg.seed.length)
        gc.2.messageKeys
        (fun mkg _ => PhaseCreditSpec.rustAlloc_optLarge hM (by decide))
      exact PhaseCreditSpec.append_eq_self hbuf hseeds
  have h12 := PhaseCreditSpec.append_eq_self hsrk hpriv
  have h123 := PhaseCreditSpec.append_eq_self h12 hck
  have h1234 := PhaseCreditSpec.append_eq_self h123 hmks
  exact h1234

theorem PhaseCreditSpec.senderChainClone {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : SenderChainGhost) (sc : SenderChain) :
    PhaseCreditSpec M (SenderChainCloneEnv g sc)
      (chainCloneCum (senderChainAsProtoGhost g sc))
      (chainCloneLarge M (senderChainAsProtoGhost g sc))
      (chainCloneLarge M (senderChainAsProtoGhost g sc))
      (chainCloneMaxReq (senderChainAsProtoGhost g sc)) :=
  PhaseCreditSpec.chainClone hM (senderChainAsProtoGhost g sc)

/-! ## 3. Full `SessionStructure::clone` (`SegCloneEnv G st`) Symbolic Credit Bound -/

def segCloneCum (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Nat :=
  vecCloneCum G.localIk.bytes.length +
  vecCloneCum G.remoteIk.bytes.length +
  (2 * 32 + 9539) +
  (match G.sender, st.senderChain with
   | some gs, some sc => chainCloneCum (senderChainAsProtoGhost gs sc)
   | _, _ => 0) +
  (if st.receiverChains = [] then 0
   else (2 * (104 * st.receiverChains.length) + 9539) +
     ((G.chains.zip st.receiverChains).map chainCloneCum).sum) +
  vecCloneCum (optTailCloneLen G.pending) +
  vecCloneCum (optTailCloneLen G.kyber) +
  vecCloneCum G.alice.bytes.length +
  vecCloneCum st.pqRatchetState.length

def segCloneLarge (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Nat :=
  vecCloneLarge M G.localIk.bytes.length +
  vecCloneLarge M G.remoteIk.bytes.length +
  optLargeCost M 32 +
  (match G.sender, st.senderChain with
   | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
   | _, _ => 0) +
  (if st.receiverChains = [] then 0
   else optLargeCost M (104 * st.receiverChains.length) +
     ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum) +
  vecCloneLarge M (optTailCloneLen G.pending) +
  vecCloneLarge M (optTailCloneLen G.kyber) +
  vecCloneLarge M G.alice.bytes.length +
  vecCloneLarge M st.pqRatchetState.length

def segCloneMaxReq (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Nat :=
  let r1 := max (max G.localIk.bytes.length G.remoteIk.bytes.length) 32
  let r2 := match G.sender, st.senderChain with
    | some gs, some sc => chainCloneMaxReq (senderChainAsProtoGhost gs sc)
    | _, _ => 0
  let r3 := max (104 * st.receiverChains.length)
    (((G.chains.zip st.receiverChains).map chainCloneMaxReq).foldr max 0)
  let r4 := max (max (optTailCloneLen G.pending) (optTailCloneLen G.kyber))
    (max G.alice.bytes.length st.pqRatchetState.length)
  max (max (max r1 r2) r3) r4

private theorem segCloneMaxReq_eq (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    max (max (max (max (max (max (max (max
      G.localIk.bytes.length
      G.remoteIk.bytes.length)
      32)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneMaxReq (senderChainAsProtoGhost gs sc)
       | _, _ => 0))
      (max (104 * st.receiverChains.length)
        (((G.chains.zip st.receiverChains).map chainCloneMaxReq).foldr max 0)))
      (optTailCloneLen G.pending))
      (optTailCloneLen G.kyber))
      G.alice.bytes.length)
      st.pqRatchetState.length =
    segCloneMaxReq G st := by
  unfold segCloneMaxReq
  dsimp only
  cases G.sender <;> cases st.senderChain <;> simp only [Nat.max_assoc]

/-- Symbolic `PhaseCreditSpec` for `SegCloneEnv G st` (`evs = segCloneEvents G st`). -/
theorem PhaseCreditSpec.segClone {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseCreditSpec M (SegCloneEnv G st)
      (segCloneCum G st) (segCloneLarge M G st) (segCloneLarge M G st) (segCloneMaxReq G st) := by
  have hloc := PhaseCreditSpec.vecClone hM G.localIk
  have hrem := PhaseCreditSpec.vecClone hM G.remoteIk
  have hroot := PhaseCreditSpec.rustAlloc_optLarge hM (req := 32) (al := 1) (by decide)
  have hsnd : PhaseCreditSpec M
      (· = match G.sender, st.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneCum (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneMaxReq (senderChainAsProtoGhost gs sc)
       | _, _ => 0) := by
    cases G.sender <;> cases st.senderChain
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.nil M
    · rename_i gs sc
      exact PhaseCreditSpec.senderChainClone hM gs sc
  have hrc : PhaseCreditSpec M
      (· = if st.receiverChains = [] then []
           else rustAllocEvents (104 * st.receiverChains.length) 8 ++
             (G.chains.zip st.receiverChains).flatMap chainCloneEvents)
      (if st.receiverChains = [] then 0
       else (2 * (104 * st.receiverChains.length) + 9539) +
         ((G.chains.zip st.receiverChains).map chainCloneCum).sum)
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum)
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum)
      (max (104 * st.receiverChains.length)
        (((G.chains.zip st.receiverChains).map chainCloneMaxReq).foldr max 0)) := by
    split
    · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
    · have hbuf := PhaseCreditSpec.rustAlloc_optLarge hM
        (req := 104 * st.receiverChains.length) (al := 8) (by decide)
      have hchains := PhaseCreditSpec.flatMap_eq_self
        chainCloneEvents chainCloneCum (chainCloneLarge M) chainCloneMaxReq
        (G.chains.zip st.receiverChains)
        (fun gc _ => PhaseCreditSpec.chainClone hM gc)
      exact PhaseCreditSpec.append_eq_self hbuf hchains
  have hpend := PhaseCreditSpec.optTailClone hM G.pending
  have hkyb := PhaseCreditSpec.optTailClone hM G.kyber
  have halice := PhaseCreditSpec.vecClone hM G.alice
  have hpq : PhaseCreditSpec M
      (· = if st.pqRatchetState.length = 0 then []
           else rustAllocEvents st.pqRatchetState.length 1)
      (vecCloneCum st.pqRatchetState.length)
      (vecCloneLarge M st.pqRatchetState.length)
      (vecCloneLarge M st.pqRatchetState.length)
      st.pqRatchetState.length := by
    unfold vecCloneCum vecCloneLarge
    exact (PhaseCreditSpec.condRustAlloc_optLarge hM
      (p := st.pqRatchetState.length = 0)
      (req := st.pqRatchetState.length) (al := 1) (by decide)).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)
  have s1 := PhaseCreditSpec.append_eq_self hloc hrem
  have s2 := PhaseCreditSpec.append_eq_self s1 hroot
  have s3 := PhaseCreditSpec.append_eq_self s2 hsnd
  have s4 := PhaseCreditSpec.append_eq_self s3 hrc
  have s5 := PhaseCreditSpec.append_eq_self s4 hpend
  have s6 := PhaseCreditSpec.append_eq_self s5 hkyb
  have s7 := PhaseCreditSpec.append_eq_self s6 halice
  have s8 := PhaseCreditSpec.append_eq_self s7 hpq
  unfold SegCloneEnv segCloneEvents segCloneCum segCloneLarge
  exact s8.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_of_eq (segCloneMaxReq_eq G st))

/-! ## 4. Exact-Order `drop_glue<SessionStructure>` `sc = 63` Free Cancellation -/

/-- Exact deallocation events of `drop_glue<Vec<MessageKey>>` on a freshly cloned `messageKeys`
list (`cap = mks.length`): per-element `seed` drops followed by the `104 * mks.length` buffer. -/
def dropClonedMessageKeysEvents (mks : List MessageKeyGenerator) : List AllocEvent :=
  if mks = [] then []
  else
    mks.flatMap (fun mkg => if mkg.seed.length = 0 then [] else rustDeallocEvents mkg.seed.length 1) ++
      rustDeallocEvents (104 * mks.length) 8

/-- Exact deallocation events of `drop_glue<Chain>` on a freshly cloned `(gc, rc)` in Block-`2`/`3`
drop order (`srk`, `priv`, `chainKey`, `messageKeys`). -/
def dropClonedChainEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  (if gc.1.srk.bytes.length = 0 then [] else rustDeallocEvents gc.1.srk.bytes.length 1) ++
  (if gc.1.priv.bytes.length = 0 then [] else rustDeallocEvents gc.1.priv.bytes.length 1) ++
  (match gc.2.chainKey with | none => [] | some _ => rustDeallocEvents 32 1) ++
  dropClonedMessageKeysEvents gc.2.messageKeys

/-- Exact deallocation events of `drop_glue<SessionStructure>` on a freshly cloned `(G, st)` in
Block-`6` (`DropSsLocal1`) drop order:
1. `localIk`, `remoteIk`, `rootKey` (`ssFirst3HeadersAt`);
2. `receiverChains` (`drop_glue<Vec<Chain>>`: each `Chain`, then `104 * rc.length` outer buffer);
3. `alice`, `pqRatchetState` (`pqPart`);
4. `senderChain`, `pending`, `kyber` (`ssTail3HeadersAt`). -/
def dropClonedSessionEvents (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent :=
  (if G.localIk.bytes.length = 0 then [] else rustDeallocEvents G.localIk.bytes.length 1) ++
  (if G.remoteIk.bytes.length = 0 then [] else rustDeallocEvents G.remoteIk.bytes.length 1) ++
  rustDeallocEvents 32 1 ++
  (if st.receiverChains = [] then []
   else (G.chains.zip st.receiverChains).flatMap dropClonedChainEvents ++
     rustDeallocEvents (104 * st.receiverChains.length) 8) ++
  (if G.alice.bytes.length = 0 then [] else rustDeallocEvents G.alice.bytes.length 1) ++
  (if st.pqRatchetState.length = 0 then [] else rustDeallocEvents st.pqRatchetState.length 1) ++
  (match G.sender, st.senderChain with
   | some gs, some sc => dropClonedChainEvents (senderChainAsProtoGhost gs sc)
   | _, _ => []) ++
  (if optTailCloneLen G.pending = 0 then [] else rustDeallocEvents (optTailCloneLen G.pending) 1) ++
  (if optTailCloneLen G.kyber = 0 then [] else rustDeallocEvents (optTailCloneLen G.kyber) 1)

theorem DeallocCreditSpec.dropClonedChain (M : AllocCostModel) [HasFineReallocCredit M]
    (gc : ChainGhost × ReceiverChain)
    (hseeds : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length = 0 → optLargeCost M mkg.seed.length = 0 :=
      by intro mkg _ h0; rw [h0, optLargeCost_zero]) :
    DeallocCreditSpec M (· = dropClonedChainEvents gc) (chainCloneLarge M gc) := by
  have hsrk : DeallocCreditSpec M
      (· = if gc.1.srk.bytes.length = 0 then [] else rustDeallocEvents gc.1.srk.bytes.length 1)
      (vecCloneLarge M gc.1.srk.bytes.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hpriv : DeallocCreditSpec M
      (· = if gc.1.priv.bytes.length = 0 then [] else rustDeallocEvents gc.1.priv.bytes.length 1)
      (vecCloneLarge M gc.1.priv.bytes.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hck : DeallocCreditSpec M
      (· = match gc.2.chainKey with | none => [] | some _ => rustDeallocEvents 32 1)
      (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32) := by
    cases gc.2.chainKey with
    | none => exact DeallocCreditSpec.nil M
    | some _ => exact DeallocCreditSpec.free_optLarge M (by decide)
  have hmks : DeallocCreditSpec M
      (· = dropClonedMessageKeysEvents gc.2.messageKeys)
      (if gc.2.messageKeys = [] then 0
       else optLargeCost M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum) := by
    unfold dropClonedMessageKeysEvents
    split
    · exact DeallocCreditSpec.nil M
    · have hseeds_spec := DeallocCreditSpec.flatMap_eq
        (fun mkg : MessageKeyGenerator =>
          if mkg.seed.length = 0 then [] else rustDeallocEvents mkg.seed.length 1)
        (fun mkg => optLargeCost M mkg.seed.length)
        gc.2.messageKeys
        (fun mkg hmkg => by
          have hc := DeallocCreditSpec.condFree_optLarge M
            (p := mkg.seed.length = 0) (req := mkg.seed.length) (al := 1) (by decide)
          refine hc.mono ?_
          split
          · rename_i h0
            rw [hseeds mkg hmkg h0]
          · exact Nat.le_refl _)
      have hbuf := DeallocCreditSpec.free_optLarge M
        (req := 104 * gc.2.messageKeys.length) (al := 8) (by decide)
      exact (DeallocCreditSpec.append_eq hseeds_spec hbuf).mono (by omega)
  have d12 := DeallocCreditSpec.append_eq hsrk hpriv
  have d123 := DeallocCreditSpec.append_eq d12 hck
  exact DeallocCreditSpec.append_eq d123 hmks

private theorem dropClonedSession_credit_ge (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    segCloneLarge M G st ≤
      vecCloneLarge M G.localIk.bytes.length +
      vecCloneLarge M G.remoteIk.bytes.length +
      optLargeCost M 32 +
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum) +
      vecCloneLarge M G.alice.bytes.length +
      vecCloneLarge M st.pqRatchetState.length +
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0) +
      vecCloneLarge M (optTailCloneLen G.pending) +
      vecCloneLarge M (optTailCloneLen G.kyber) := by
  unfold segCloneLarge
  cases G.sender <;> cases st.senderChain <;> dsimp only <;> omega

/-- Exact-order deallocation of a freshly cloned `SessionStructure` credits back
`segCloneLarge M G st` from `liveLarge` without reordering. -/
theorem DeallocCreditSpec.dropClonedSession (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    DeallocCreditSpec M (· = dropClonedSessionEvents G st) (segCloneLarge M G st) := by
  have hloc : DeallocCreditSpec M
      (· = if G.localIk.bytes.length = 0 then [] else rustDeallocEvents G.localIk.bytes.length 1)
      (vecCloneLarge M G.localIk.bytes.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hrem : DeallocCreditSpec M
      (· = if G.remoteIk.bytes.length = 0 then [] else rustDeallocEvents G.remoteIk.bytes.length 1)
      (vecCloneLarge M G.remoteIk.bytes.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hroot := DeallocCreditSpec.free_optLarge M (req := 32) (al := 1) (by decide)
  have hrc : DeallocCreditSpec M
      (· = if st.receiverChains = [] then []
           else (G.chains.zip st.receiverChains).flatMap dropClonedChainEvents ++
             rustDeallocEvents (104 * st.receiverChains.length) 8)
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum) := by
    split
    · exact DeallocCreditSpec.nil M
    · have hchains := DeallocCreditSpec.flatMap_eq
        dropClonedChainEvents (chainCloneLarge M) (G.chains.zip st.receiverChains)
        (fun gc _ => DeallocCreditSpec.dropClonedChain M gc)
      have hbuf := DeallocCreditSpec.free_optLarge M
        (req := 104 * st.receiverChains.length) (al := 8) (by decide)
      exact (DeallocCreditSpec.append_eq hchains hbuf).mono (by omega)
  have halice : DeallocCreditSpec M
      (· = if G.alice.bytes.length = 0 then [] else rustDeallocEvents G.alice.bytes.length 1)
      (vecCloneLarge M G.alice.bytes.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hpq : DeallocCreditSpec M
      (· = if st.pqRatchetState.length = 0 then [] else rustDeallocEvents st.pqRatchetState.length 1)
      (vecCloneLarge M st.pqRatchetState.length) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hsnd : DeallocCreditSpec M
      (· = match G.sender, st.senderChain with
           | some gs, some sc => dropClonedChainEvents (senderChainAsProtoGhost gs sc)
           | _, _ => [])
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0) := by
    cases G.sender <;> cases st.senderChain
    · exact DeallocCreditSpec.nil M
    · exact DeallocCreditSpec.nil M
    · exact DeallocCreditSpec.nil M
    · rename_i gs sc
      exact DeallocCreditSpec.dropClonedChain M (senderChainAsProtoGhost gs sc)
  have hpend : DeallocCreditSpec M
      (· = if optTailCloneLen G.pending = 0 then []
           else rustDeallocEvents (optTailCloneLen G.pending) 1)
      (vecCloneLarge M (optTailCloneLen G.pending)) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have hkyb : DeallocCreditSpec M
      (· = if optTailCloneLen G.kyber = 0 then []
           else rustDeallocEvents (optTailCloneLen G.kyber) 1)
      (vecCloneLarge M (optTailCloneLen G.kyber)) :=
    DeallocCreditSpec.condFree_optLarge M (by decide)
  have d1 := DeallocCreditSpec.append_eq hloc hrem
  have d2 := DeallocCreditSpec.append_eq d1 hroot
  have d3 := DeallocCreditSpec.append_eq d2 hrc
  have d4 := DeallocCreditSpec.append_eq d3 halice
  have d5 := DeallocCreditSpec.append_eq d4 hpq
  have d6 := DeallocCreditSpec.append_eq d5 hsnd
  have d7 := DeallocCreditSpec.append_eq d6 hpend
  have d8 := DeallocCreditSpec.append_eq d7 hkyb
  unfold dropClonedSessionEvents
  exact d8.mono (dropClonedSession_credit_ge M G st)

/-- Cloning `SessionStructure` (`SegCloneEnv G st`), running `E_body` while the clone is live, and
dropping the clone (`dropClonedSessionEvents G st`) in binary call order leaves `Δlive = l_b` and
`Δpeak = segCloneLarge M G st + p_b`. -/
theorem PhaseCreditSpec.segClone_body_drop_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G st) E_body) (· = dropClonedSessionEvents G st))
      (segCloneCum G st + c_b)
      l_b
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) := by
  have hclone := PhaseCreditSpec.segClone hM G st
  have h12 : PhaseCreditSpec M (ConcatEnv (SegCloneEnv G st) E_body)
      (segCloneCum G st + c_b)
      (l_b + segCloneLarge M G st)
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) :=
    (hclone.concat hbody).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  exact h12.concat_dealloc_cancel (DeallocCreditSpec.dropClonedSession M G st)

/-! ## 5. Tight Per-Size-Class Clone Credit -/

section TightCloneCredit

open VerifiedLibraries.Mallocng.Proofs (nominalSlotCap sizeToClassUnits sizeToClass_spec)
open LibsignalBinary.Heap.Fine (
  FineScale MmapThresholdReq coarseGrpWtS coarseSlotWt declCost63
  fineCostModel fineSmallAllocCost fineSmallReallocCost
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  fineCostModel_largeMetaCost_eq fineCostModel_smallMaxReq_eq reqMinOfClass
  smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44
)
open LibsignalBinary.Heap.Fine.ClientIntegration (smallAllocCost_le_3506_of_kyber_range)

/-- Exact regime-aware `cumSmall` charge of `rustAllocEvents req al` (`al ≤ 16`):
`smallAllocCost M req` when `req ≤ smallMaxReq M`, and `largeMetaCost M` when `smallMaxReq M < req`. -/
def rustAllocTightCum (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then HasFineReallocCredit.smallAllocCost M req
  else HasFineReallocCredit.largeMetaCost M

/-- Exact regime-aware `cumSmall` charge of a conditional non-empty slice clone (`0` when `len = 0`,
`rustAllocTightCum M len` otherwise; matches `tryCloneSmallDelta` on `fineCostModel`). -/
def tryCloneSmallDelta (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len = 0 then 0 else rustAllocTightCum M len

/-- Tight counterpart of `vecCloneCum`. -/
abbrev vecCloneTightCum (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  tryCloneSmallDelta M len

/-- Tight regime-uniform `PhaseCreditSpec` for `rustAllocEvents req al` (`al ≤ 16`). -/
theorem PhaseCreditSpec.rustAlloc_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (rustAllocTightCum M req) (optLargeCost M req) (optLargeCost M req) req := by
  unfold rustAllocTightCum optLargeCost
  split
  · rename_i hle
    exact PhaseCreditSpec.rustAlloc_small_any hM hal hle
  · rename_i hnot
    exact PhaseCreditSpec.rustAlloc_large M hal (Nat.lt_of_not_ge hnot)

/-- Conditional `if p then [] else rustAllocEvents req al` tight allocation bound (`0` when `p`). -/
theorem PhaseCreditSpec.condRustAlloc_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {p : Prop} [Decidable p] {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = if p then [] else rustAllocEvents req al)
      (if p then 0 else rustAllocTightCum M req)
      (if p then 0 else optLargeCost M req)
      (if p then 0 else optLargeCost M req)
      (if p then 0 else req) := by
  split
  · exact PhaseCreditSpec.nil M
  · exact PhaseCreditSpec.rustAlloc_tight hM hal

theorem PhaseCreditSpec.vecClone_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (v : VecGhost) :
    PhaseCreditSpec M (· = vecCloneEvents v)
      (vecCloneTightCum M v.bytes.length)
      (vecCloneLarge M v.bytes.length)
      (vecCloneLarge M v.bytes.length)
      v.bytes.length := by
  unfold vecCloneEvents vecCloneTightCum tryCloneSmallDelta vecCloneLarge
  exact (PhaseCreditSpec.condRustAlloc_tight hM (p := v.bytes.length = 0)
    (req := v.bytes.length) (al := 1) (by decide)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)

theorem PhaseCreditSpec.optTailClone_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (o : Option TailVecGhost) :
    PhaseCreditSpec M (· = optTailCloneEvents o)
      (vecCloneTightCum M (optTailCloneLen o))
      (vecCloneLarge M (optTailCloneLen o))
      (vecCloneLarge M (optTailCloneLen o))
      (optTailCloneLen o) := by
  cases o with
  | none =>
    simpa [optTailCloneEvents, optTailCloneLen, vecCloneTightCum, tryCloneSmallDelta, vecCloneLarge]
      using PhaseCreditSpec.nil M
  | some g =>
    simpa [optTailCloneEvents, optTailCloneLen] using PhaseCreditSpec.vecClone_tight hM g.vec

/-- Tight cumulative small/metadata bound for `chainCloneEvents gc`. -/
def chainCloneTightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (gc : ChainGhost × ReceiverChain) : Nat :=
  tryCloneSmallDelta M gc.1.srk.bytes.length +
  tryCloneSmallDelta M gc.1.priv.bytes.length +
  (match gc.2.chainKey with | none => 0 | some _ => rustAllocTightCum M 32) +
  (if gc.2.messageKeys = [] then 0
   else rustAllocTightCum M (104 * gc.2.messageKeys.length) +
     (gc.2.messageKeys.map fun mkg => rustAllocTightCum M mkg.seed.length).sum)

theorem PhaseCreditSpec.chainClone_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (gc : ChainGhost × ReceiverChain) :
    PhaseCreditSpec M (ChainCloneEnv gc)
      (chainCloneTightCum M gc) (chainCloneLarge M gc)
      (chainCloneLarge M gc) (chainCloneMaxReq gc) := by
  have hsrk := PhaseCreditSpec.vecClone_tight hM gc.1.srk
  have hpriv := PhaseCreditSpec.vecClone_tight hM gc.1.priv
  have hck : PhaseCreditSpec M
      (· = match gc.2.chainKey with | none => [] | some _ => rustAllocEvents 32 1)
      (match gc.2.chainKey with | none => 0 | some _ => rustAllocTightCum M 32)
      (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32)
      (match gc.2.chainKey with | none => 0 | some _ => optLargeCost M 32)
      32 := by
    cases gc.2.chainKey with
    | none => exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | some _ => exact PhaseCreditSpec.rustAlloc_tight hM (by decide)
  have hmks : PhaseCreditSpec M
      (· = if gc.2.messageKeys = [] then []
           else rustAllocEvents (104 * gc.2.messageKeys.length) 8 ++
             gc.2.messageKeys.flatMap (fun mkg => rustAllocEvents mkg.seed.length 1))
      (if gc.2.messageKeys = [] then 0
       else rustAllocTightCum M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => rustAllocTightCum M mkg.seed.length).sum)
      (if gc.2.messageKeys = [] then 0
       else optLargeCost M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum)
      (if gc.2.messageKeys = [] then 0
       else optLargeCost M (104 * gc.2.messageKeys.length) +
         (gc.2.messageKeys.map fun mkg => optLargeCost M mkg.seed.length).sum)
      (max (104 * gc.2.messageKeys.length)
        ((gc.2.messageKeys.map fun mkg => mkg.seed.length).foldr max 0)) := by
    split
    · exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · have hbuf := PhaseCreditSpec.rustAlloc_tight hM
        (req := 104 * gc.2.messageKeys.length) (al := 8) (by decide)
      have hseeds := PhaseCreditSpec.flatMap_eq_self
        (fun mkg : MessageKeyGenerator => rustAllocEvents mkg.seed.length 1)
        (fun mkg => rustAllocTightCum M mkg.seed.length)
        (fun mkg => optLargeCost M mkg.seed.length)
        (fun mkg => mkg.seed.length)
        gc.2.messageKeys
        (fun mkg _ => PhaseCreditSpec.rustAlloc_tight hM (by decide))
      exact PhaseCreditSpec.append_eq_self hbuf hseeds
  have h12 := PhaseCreditSpec.append_eq_self hsrk hpriv
  have h123 := PhaseCreditSpec.append_eq_self h12 hck
  exact PhaseCreditSpec.append_eq_self h123 hmks

theorem PhaseCreditSpec.senderChainClone_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : SenderChainGhost) (sc : SenderChain) :
    PhaseCreditSpec M (SenderChainCloneEnv g sc)
      (chainCloneTightCum M (senderChainAsProtoGhost g sc))
      (chainCloneLarge M (senderChainAsProtoGhost g sc))
      (chainCloneLarge M (senderChainAsProtoGhost g sc))
      (chainCloneMaxReq (senderChainAsProtoGhost g sc)) :=
  PhaseCreditSpec.chainClone_tight hM (senderChainAsProtoGhost g sc)

/-- Tight cumulative small/metadata bound for `SegCloneEnv G st`. -/
def segCloneTightCum (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Nat :=
  tryCloneSmallDelta M G.localIk.bytes.length +
  tryCloneSmallDelta M G.remoteIk.bytes.length +
  rustAllocTightCum M 32 +
  (match G.sender, st.senderChain with
   | some gs, some sc => chainCloneTightCum M (senderChainAsProtoGhost gs sc)
   | _, _ => 0) +
  (if st.receiverChains = [] then 0
   else rustAllocTightCum M (104 * st.receiverChains.length) +
     ((G.chains.zip st.receiverChains).map (chainCloneTightCum M)).sum) +
  tryCloneSmallDelta M (optTailCloneLen G.pending) +
  tryCloneSmallDelta M (optTailCloneLen G.kyber) +
  tryCloneSmallDelta M G.alice.bytes.length +
  tryCloneSmallDelta M st.pqRatchetState.length

/-- Tight symbolic `PhaseCreditSpec` for `SegCloneEnv G st`. -/
theorem PhaseCreditSpec.segClone_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    PhaseCreditSpec M (SegCloneEnv G st)
      (segCloneTightCum M G st) (segCloneLarge M G st)
      (segCloneLarge M G st) (segCloneMaxReq G st) := by
  have hloc := PhaseCreditSpec.vecClone_tight hM G.localIk
  have hrem := PhaseCreditSpec.vecClone_tight hM G.remoteIk
  have hroot := PhaseCreditSpec.rustAlloc_tight hM (req := 32) (al := 1) (by decide)
  have hsnd : PhaseCreditSpec M
      (· = match G.sender, st.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneTightCum M (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneLarge M (senderChainAsProtoGhost gs sc)
       | _, _ => 0)
      (match G.sender, st.senderChain with
       | some gs, some sc => chainCloneMaxReq (senderChainAsProtoGhost gs sc)
       | _, _ => 0) := by
    cases G.sender <;> cases st.senderChain
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.nil M
    · exact PhaseCreditSpec.nil M
    · rename_i gs sc
      exact PhaseCreditSpec.senderChainClone_tight hM gs sc
  have hrc : PhaseCreditSpec M
      (· = if st.receiverChains = [] then []
           else rustAllocEvents (104 * st.receiverChains.length) 8 ++
             (G.chains.zip st.receiverChains).flatMap chainCloneEvents)
      (if st.receiverChains = [] then 0
       else rustAllocTightCum M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneTightCum M)).sum)
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum)
      (if st.receiverChains = [] then 0
       else optLargeCost M (104 * st.receiverChains.length) +
         ((G.chains.zip st.receiverChains).map (chainCloneLarge M)).sum)
      (max (104 * st.receiverChains.length)
        (((G.chains.zip st.receiverChains).map chainCloneMaxReq).foldr max 0)) := by
    split
    · exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · have hbuf := PhaseCreditSpec.rustAlloc_tight hM
        (req := 104 * st.receiverChains.length) (al := 8) (by decide)
      have hchains := PhaseCreditSpec.flatMap_eq_self
        chainCloneEvents (chainCloneTightCum M) (chainCloneLarge M) chainCloneMaxReq
        (G.chains.zip st.receiverChains)
        (fun gc _ => PhaseCreditSpec.chainClone_tight hM gc)
      exact PhaseCreditSpec.append_eq_self hbuf hchains
  have hpend := PhaseCreditSpec.optTailClone_tight hM G.pending
  have hkyb := PhaseCreditSpec.optTailClone_tight hM G.kyber
  have halice := PhaseCreditSpec.vecClone_tight hM G.alice
  have hpq : PhaseCreditSpec M
      (· = if st.pqRatchetState.length = 0 then []
           else rustAllocEvents st.pqRatchetState.length 1)
      (tryCloneSmallDelta M st.pqRatchetState.length)
      (vecCloneLarge M st.pqRatchetState.length)
      (vecCloneLarge M st.pqRatchetState.length)
      st.pqRatchetState.length := by
    unfold tryCloneSmallDelta vecCloneLarge
    exact (PhaseCreditSpec.condRustAlloc_tight hM
      (p := st.pqRatchetState.length = 0)
      (req := st.pqRatchetState.length) (al := 1) (by decide)).mono
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by split <;> omega)
  have s1 := PhaseCreditSpec.append_eq_self hloc hrem
  have s2 := PhaseCreditSpec.append_eq_self s1 hroot
  have s3 := PhaseCreditSpec.append_eq_self s2 hsnd
  have s4 := PhaseCreditSpec.append_eq_self s3 hrc
  have s5 := PhaseCreditSpec.append_eq_self s4 hpend
  have s6 := PhaseCreditSpec.append_eq_self s5 hkyb
  have s7 := PhaseCreditSpec.append_eq_self s6 halice
  have s8 := PhaseCreditSpec.append_eq_self s7 hpq
  unfold SegCloneEnv segCloneEvents segCloneTightCum segCloneLarge
  exact s8.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_of_eq (segCloneMaxReq_eq G st))

/-- Tight `SessionStructure::clone` + body + `drop_glue` `sc = 63` cancellation. -/
theorem PhaseCreditSpec.segClone_body_drop_cancel_tight
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (SegCloneEnv G st) E_body) (· = dropClonedSessionEvents G st))
      (segCloneTightCum M G st + c_b)
      l_b
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) := by
  have hclone := PhaseCreditSpec.segClone_tight hM G st
  have h12 : PhaseCreditSpec M (ConcatEnv (SegCloneEnv G st) E_body)
      (segCloneTightCum M G st + c_b)
      (l_b + segCloneLarge M G st)
      (segCloneLarge M G st + p_b)
      (max (segCloneMaxReq G st) r_b) :=
    (hclone.concat hbody).mono
      (Nat.le_refl _) (Nat.le_of_eq (Nat.add_comm _ _))
      (Nat.le_trans (Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩) (Nat.le_refl _))
      (Nat.le_refl _)
  exact h12.concat_dealloc_cancel (DeallocCreditSpec.dropClonedSession M G st)

/-! ### Concrete `fineCostModel` Size-Class Cap & Point Lemmas -/

def fineAllocClassWt (sc : Nat) : Nat :=
  coarseSlotWt sc + (122 * coarseGrpWtS sc + FineScale - 1) / FineScale

def fineReallocClassMax (sc cap : Nat) : Nat :=
  max (coarseSlotWt sc) (min cap (nominalSlotCap sc) + 8195) +
    (122 * max (coarseGrpWtS sc) FineScale + FineScale - 1) / FineScale

private def checkFineTightClassCaps : Bool :=
  (List.range 48).all fun sc =>
    let rMin := reqMinOfClass sc
    let nCap := nominalSlotCap sc
    let aWt := fineAllocClassWt sc
    decide (
      aWt ≤ 143484 ∧
      fineReallocClassMax sc 131051 ≤ 143484 ∧
      (rMin ≤ 64 → aWt ≤ 1607) ∧
      (rMin ≤ 192 → aWt ≤ 9789) ∧
      (rMin ≤ 256 → aWt ≤ 9789 ∧ fineReallocClassMax sc 256 ≤ 9789) ∧
      (rMin ≤ 520 → aWt ≤ 9789) ∧
      (192 ≤ nCap → rMin ≤ 768 → fineReallocClassMax sc 768 ≤ 9085) ∧
      (rMin ≤ 2048 → aWt ≤ 9789 ∧ fineReallocClassMax sc 2048 ≤ 10365) ∧
      (rMin ≤ 8192 → aWt ≤ 12410 ∧ fineReallocClassMax sc 8192 ≤ 16509))

private theorem checkFineTightClassCaps_true : checkFineTightClassCaps = true := by
  decide +kernel

private def fineTightPointPairs : List (Nat × Nat) :=
  [(24, 488), (32, 738), (33, 738), (192, 8186), (520, 4436), (1569, 2792)]

private def checkFineTightPoints : Bool :=
  fineTightPointPairs.all fun (req, expected) =>
    fineSmallAllocCost req == expected

private theorem checkFineTightPoints_true : checkFineTightPoints = true := by
  decide +kernel

private theorem extractFineAllocPoint {req expected : Nat}
    (hmem : (req, expected) ∈ fineTightPointPairs) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  have hcell := List.all_eq_true.mp checkFineTightPoints_true (req, expected) hmem
  exact of_decide_eq_true hcell

theorem fineSmallAllocCost_24 : HasFineReallocCredit.smallAllocCost fineCostModel 24 = 488 :=
  extractFineAllocPoint (by decide)

theorem fineSmallAllocCost_32 : HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 :=
  extractFineAllocPoint (by decide)

theorem fineSmallAllocCost_33 : HasFineReallocCredit.smallAllocCost fineCostModel 33 = 738 :=
  extractFineAllocPoint (by decide)

theorem fineSmallAllocCost_192 : HasFineReallocCredit.smallAllocCost fineCostModel 192 = 8186 :=
  extractFineAllocPoint (by decide)

theorem fineSmallAllocCost_520 : HasFineReallocCredit.smallAllocCost fineCostModel 520 = 4436 :=
  extractFineAllocPoint (by decide)

theorem fineSmallAllocCost_1569 : HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 :=
  extractFineAllocPoint (by decide)

theorem classBounds_of_le_mmap {req : Nat} (hreq : req ≤ MmapThresholdReq) :
    let sc0 := sizeToClassUnits ((req + 3) / 16)
    sc0 < 48 ∧ reqMinOfClass sc0 ≤ req ∧ req ≤ nominalSlotCap sc0 := by
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hreq; exact hreq)
  dsimp only at hspec ⊢
  refine ⟨hspec.1, ?_, hspec.2.1⟩
  unfold reqMinOfClass
  rcases hspec.2.2 with h0 | hprev
  · simp [h0]
  · split <;> omega

private theorem fineSmallReallocCost_le_classMax {req cap : Nat}
    (hmmap : req ≤ MmapThresholdReq) (hcap : req ≤ cap) :
    HasFineReallocCredit.smallReallocCost fineCostModel req ≤
      fineReallocClassMax (sizeToClassUnits ((req + 3) / 16)) cap := by
  change fineSmallReallocCost req ≤ _
  obtain ⟨_, _, hnom⟩ := classBounds_of_le_mmap hmmap
  unfold fineSmallReallocCost fineReallocClassMax
  simp only [hmmap, ↓reduceIte]
  have hmin : req ≤ min cap (nominalSlotCap (sizeToClassUnits ((req + 3) / 16))) :=
    Nat.le_min.mpr ⟨hcap, hnom⟩
  have hc63 : declCost63 req 16 ≤
      min cap (nominalSlotCap (sizeToClassUnits ((req + 3) / 16))) + 8195 := by
    unfold declCost63
    omega
  exact Nat.add_le_add
    (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans hc63 (Nat.le_max_right _ _)⟩)
    (Nat.le_refl _)

/-- Global small-allocation ceiling on `fineCostModel`: `smallAllocCost req ≤ 143,484` for all
`req ≤ 135,167`. -/
theorem fineSmallAllocCost_le_143484 {req : Nat}
    (hle : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 143484 := by
  rw [fineCostModel_smallMaxReq_eq] at hle
  change fineSmallAllocCost req ≤ 143484
  unfold fineSmallAllocCost
  by_cases hm : req ≤ MmapThresholdReq
  · simp only [hm, ↓reduceIte]
    obtain ⟨hsc, _, _⟩ := classBounds_of_le_mmap hm
    have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
    exact (of_decide_eq_true hcell).1
  · simp only [hm, ↓reduceIte]
    have hdc : declCost63 req 16 + 122 = req + 8317 := by
      unfold declCost63
      omega
    rw [hdc]
    exact Nat.le_trans (Nat.add_le_add_right hle 8317) (by decide)

/-- Global small-reallocation ceiling on `fineCostModel`: `smallReallocCost newSz ≤ 143,484` for all
`newSz ≤ 135,167`. -/
theorem fineSmallReallocCost_le_143484 {newSz : Nat}
    (hle : newSz ≤ HasFineReallocCredit.smallMaxReq fineCostModel) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 143484 := by
  rw [fineCostModel_smallMaxReq_eq] at hle
  by_cases hm : newSz ≤ MmapThresholdReq
  · obtain ⟨hsc, _, _⟩ := classBounds_of_le_mmap hm
    have hle_cm := fineSmallReallocCost_le_classMax hm (by unfold MmapThresholdReq at hm; exact hm)
    have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
    exact Nat.le_trans hle_cm (of_decide_eq_true hcell).2.1
  · change fineSmallReallocCost newSz ≤ 143484
    unfold fineSmallReallocCost
    simp only [hm, ↓reduceIte]
    have hdc : max 0 (declCost63 newSz 16) +
        (122 * max 0 FineScale + FineScale - 1) / FineScale = newSz + 8317 := by
      have hscale : (122 * max 0 FineScale + FineScale - 1) / FineScale = 122 := by decide
      rw [hscale]
      unfold declCost63
      omega
    rw [hdc]
    exact Nat.le_trans (Nat.add_le_add_right hle 8317) (by decide)

/-- Unconditional global `cumSmall` ceiling for `rustAllocTightCum fineCostModel req` over ALL `req : Nat`:
`≤ 143,484` (small requests pay `≤ 143,484`; `sc = 63` requests pay `122`). -/
theorem rustAllocTightCum_fine_le_143484 (req : Nat) :
    rustAllocTightCum fineCostModel req ≤ 143484 := by
  unfold rustAllocTightCum
  split
  · rename_i hle
    exact fineSmallAllocCost_le_143484 hle
  · rw [fineCostModel_largeMetaCost_eq]
    decide

/-- Unconditional global `cumSmall` ceiling for `tryCloneSmallDelta fineCostModel len` over ALL `len : Nat`:
`≤ 143,484`. -/
theorem tryCloneSmallDelta_fine_le_143484 (len : Nat) :
    tryCloneSmallDelta fineCostModel len ≤ 143484 := by
  unfold tryCloneSmallDelta
  split
  · exact Nat.zero_le 143484
  · exact rustAllocTightCum_fine_le_143484 len

theorem fineSmallAllocCost_le_1607_of_le_64 {req : Nat} (hreq : req ≤ 64) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 1607 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 1607
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.1 (Nat.le_trans hrmin hreq)

theorem fineSmallAllocCost_le_9789_of_le_192 {req : Nat} (hreq : req ≤ 192) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 9789
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.2.1 (Nat.le_trans hrmin hreq)

theorem fineSmallAllocCost_le_9789_of_le_256 {req : Nat} (hreq : req ≤ 256) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 9789
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact ((of_decide_eq_true hcell).2.2.2.2.1 (Nat.le_trans hrmin hreq)).1

theorem fineSmallReallocCost_le_9789_of_le_256 {req : Nat} (hreq : req ≤ 256) :
    HasFineReallocCredit.smallReallocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcm := fineSmallReallocCost_le_classMax hm hreq
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact Nat.le_trans hcm ((of_decide_eq_true hcell).2.2.2.2.1 (Nat.le_trans hrmin hreq)).2

theorem fineSmallAllocCost_le_9789_of_le_520 {req : Nat} (hreq : req ≤ 520) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 9789
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact (of_decide_eq_true hcell).2.2.2.2.2.1 (Nat.le_trans hrmin hreq)

theorem fineSmallReallocCost_le_9085_of_192_768 {req : Nat}
    (hlo : 192 ≤ req) (hhi : req ≤ 768) :
    HasFineReallocCredit.smallReallocCost fineCostModel req ≤ 9085 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hhi (by decide)
  obtain ⟨hsc, hrmin, hnom⟩ := classBounds_of_le_mmap hm
  have hcm := fineSmallReallocCost_le_classMax hm hhi
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact Nat.le_trans hcm
    ((of_decide_eq_true hcell).2.2.2.2.2.2.1 (Nat.le_trans hlo hnom) (Nat.le_trans hrmin hhi))

theorem fineSmallAllocCost_le_9789_of_le_2048 {req : Nat} (hreq : req ≤ 2048) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 9789
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact ((of_decide_eq_true hcell).2.2.2.2.2.2.2.1 (Nat.le_trans hrmin hreq)).1

theorem fineSmallAllocCost_le_12410_of_le_8192 {req : Nat} (hreq : req ≤ 8192) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 12410 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  change fineSmallAllocCost req ≤ 12410
  unfold fineSmallAllocCost
  simp only [hm, ↓reduceIte]
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact ((of_decide_eq_true hcell).2.2.2.2.2.2.2.2 (Nat.le_trans hrmin hreq)).1

theorem fineSmallReallocCost_le_16509_of_le_8192 {req : Nat} (hreq : req ≤ 8192) :
    HasFineReallocCredit.smallReallocCost fineCostModel req ≤ 16509 := by
  have hm : req ≤ MmapThresholdReq := Nat.le_trans hreq (by decide)
  obtain ⟨hsc, hrmin, _⟩ := classBounds_of_le_mmap hm
  have hcm := fineSmallReallocCost_le_classMax hm hreq
  have hcell := List.all_eq_true.mp checkFineTightClassCaps_true _ (List.mem_range.mpr hsc)
  exact Nat.le_trans hcm ((of_decide_eq_true hcell).2.2.2.2.2.2.2.2 (Nat.le_trans hrmin hreq)).2

theorem rustAllocTightCum_fine_24 : rustAllocTightCum fineCostModel 24 = 488 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_24]

theorem rustAllocTightCum_fine_32 : rustAllocTightCum fineCostModel 32 = 738 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_32]

theorem rustAllocTightCum_fine_520 : rustAllocTightCum fineCostModel 520 = 4436 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_520]

theorem rustAllocTightCum_fine_1569 : rustAllocTightCum fineCostModel 1569 = 2792 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq]
  simp [fineSmallAllocCost_1569]

theorem rustAllocTightCum_fine_of_gt {req : Nat} (hgt : 135167 < req) :
    rustAllocTightCum fineCostModel req = 122 := by
  unfold rustAllocTightCum
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeMetaCost_eq]
  have hnot : ¬ (req ≤ 135167) := Nat.not_le.mpr hgt
  simp [hnot]

theorem tryCloneSmallDelta_fine_le_738 {len : Nat} (hlen : len ≤ 44) :
    tryCloneSmallDelta fineCostModel len ≤ 738 := by
  unfold tryCloneSmallDelta rustAllocTightCum
  split
  · exact Nat.zero_le 738
  · have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans hlen (by decide)
    simp only [hsm, ↓reduceIte]
    exact smallAllocCost_le_738_of_le_44 hlen

theorem tryCloneSmallDelta_fine_le_2792 {len : Nat} (h : len = 0 ∨ len = 1569) :
    tryCloneSmallDelta fineCostModel len ≤ 2792 := by
  rcases h with rfl | rfl
  · simp [tryCloneSmallDelta]
  · unfold tryCloneSmallDelta
    simp [rustAllocTightCum_fine_1569]

theorem rustAllocTightCum_fine_le_738 {req : Nat} (hreq : req ≤ 44) :
    rustAllocTightCum fineCostModel req ≤ 738 := by
  unfold rustAllocTightCum
  have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact Nat.le_trans hreq (by decide)
  simp only [hsm, ↓reduceIte]
  exact smallAllocCost_le_738_of_le_44 hreq

theorem tryCloneSmallDelta_fine_kyber_range_le_3506 {len : Nat}
    (h : len = 0 ∨ (1024 ≤ len ∧ len ≤ 1600)) :
    tryCloneSmallDelta fineCostModel len ≤ 3506 := by
  rcases h with rfl | ⟨hlo, hhi⟩
  · simp [tryCloneSmallDelta]
  · unfold tryCloneSmallDelta rustAllocTightCum
    have hnz : len ≠ 0 := by omega
    have hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans hhi (by decide)
    simp only [hnz, hsm, ↓reduceIte]
    exact smallAllocCost_le_3506_of_kyber_range
      (Nat.le_trans (by decide) hlo) (Nat.le_trans hhi (by decide))

theorem tryCloneSmallDelta_fine_pq_le_122 {len : Nat}
    (hpq : len = 0 ∨ 135167 < len) :
    tryCloneSmallDelta fineCostModel len ≤ 122 := by
  rcases hpq with rfl | hgt
  · simp [tryCloneSmallDelta]
  · unfold tryCloneSmallDelta
    have hnz : len ≠ 0 := by omega
    simp only [hnz, ↓reduceIte, rustAllocTightCum_fine_of_gt hgt]
    exact Nat.le_refl 122

private theorem list_map_sum_le_mul {α : Type} (f : α → Nat) (c : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, f x ≤ c) → (xs.map f).sum ≤ c * xs.length
  | [], _ => Nat.zero_le _
  | x :: xs, hall => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := hall x List.mem_cons_self
    have hxs := list_map_sum_le_mul f c xs (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    have hmul : c * (xs.length + 1) = c + c * xs.length := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rw [hmul]
    exact Nat.add_le_add hx hxs

private theorem list_map_sum_aff_le {α : Type} (f lenF : α → Nat) (a b : Nat) :
    ∀ (xs : List α),
      (∀ x ∈ xs, f x ≤ a + b * lenF x) →
      (xs.map f).sum ≤ xs.length * a + b * (xs.map lenF).sum
  | [], _ => Nat.zero_le _
  | x :: xs, hall => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := hall x List.mem_cons_self
    have hxs := list_map_sum_aff_le f lenF a b xs (fun y hy => hall y (List.mem_cons_of_mem _ hy))
    have hsum := Nat.add_le_add hx hxs
    have hrhs : (a + b * lenF x) + (xs.length * a + b * (xs.map lenF).sum) =
        (xs.length + 1) * a + b * (lenF x + (xs.map lenF).sum) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    rw [← hrhs]
    exact hsum

/-- Empty-`messageKeys` `ChainClone` tight bound on `fineCostModel`: `≤ 2,214` B (`3 × 738`). -/
theorem chainCloneTightCum_fine_empty_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length ≤ 44)
    (hpriv : gc.1.priv.bytes.length ≤ 44)
    (hmks : gc.2.messageKeys = []) :
    chainCloneTightCum fineCostModel gc ≤ 2214 := by
  unfold chainCloneTightCum
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  have h3 : (match gc.2.chainKey with | none => 0 | some _ => rustAllocTightCum fineCostModel 32) ≤ 738 := by
    cases gc.2.chainKey with
    | none => exact Nat.zero_le 738
    | some _ => rw [rustAllocTightCum_fine_32]
  simp only [hmks, ↓reduceIte, Nat.add_zero]
  exact Nat.le_trans (Nat.add_le_add (Nat.add_le_add h1 h2) h3) (by decide)

/-- Sender-chain clone tight bound on `fineCostModel`: `≤ 2,214` B whenever `srk, priv ≤ 44`. -/
theorem senderChainCloneTightCum_fine_le {gs : SenderChainGhost} {sc : SenderChain}
    (hsrk : gs.srk.bytes.length ≤ 44) (hpriv : gs.priv.bytes.length ≤ 44) :
    chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc) ≤ 2214 :=
  chainCloneTightCum_fine_empty_le hsrk hpriv rfl

/-- Heavy-`messageKeys` (`1300 ≤ len ≤ maxKeys`) `ChainClone` tight bound on `fineCostModel`:
`104 * len > 135,167` puts the `Vec<MessageKey>` buffer in `sc = 63` (`122` B meta), yielding
`chainCloneTightCum ≤ 2,336 + 738 * maxKeys` (`= 1,478,336` B at `maxKeys = 2,000`). -/
theorem chainCloneTightCum_fine_large_le {gc : ChainGhost × ReceiverChain} {maxKeys : Nat}
    (hsrk : gc.1.srk.bytes.length ≤ 44)
    (hpriv : gc.1.priv.bytes.length ≤ 44)
    (hlo : 1300 ≤ gc.2.messageKeys.length)
    (hhi : gc.2.messageKeys.length ≤ maxKeys)
    (hseeds : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ 44) :
    chainCloneTightCum fineCostModel gc ≤ 2336 + 738 * maxKeys := by
  unfold chainCloneTightCum
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  have h3 : (match gc.2.chainKey with | none => 0 | some _ => rustAllocTightCum fineCostModel 32) ≤ 738 := by
    cases gc.2.chainKey with
    | none => exact Nat.zero_le 738
    | some _ => rw [rustAllocTightCum_fine_32]
  have hne : gc.2.messageKeys ≠ [] := by
    intro heq
    rw [heq] at hlo
    exact absurd hlo (by decide)
  have hgt : 135167 < 104 * gc.2.messageKeys.length := by omega
  have hbuf : rustAllocTightCum fineCostModel (104 * gc.2.messageKeys.length) = 122 :=
    rustAllocTightCum_fine_of_gt hgt
  have hsd : (gc.2.messageKeys.map fun mkg => rustAllocTightCum fineCostModel mkg.seed.length).sum ≤
      738 * maxKeys := by
    refine Nat.le_trans
      (list_map_sum_le_mul (fun mkg => rustAllocTightCum fineCostModel mkg.seed.length) 738
        gc.2.messageKeys (fun mkg hm => rustAllocTightCum_fine_le_738 (hseeds mkg hm)))
      (Nat.mul_le_mul_left 738 hhi)
  simp only [hne, ↓reduceIte, hbuf]
  have h123 := Nat.add_le_add (Nat.add_le_add h1 h2) h3
  have hpre : (738 + 738 + 738) + (122 + 738 * maxKeys) = 2336 + 738 * maxKeys := by
    rw [← Nat.add_assoc ((738 + 738 + 738)), show (738 + 738 + 738) + 122 = 2336 by decide]
  rw [← hpre]
  exact Nat.add_le_add h123 (Nat.add_le_add (Nat.le_refl 122) hsd)

/-- General `ChainClone` tight bound on `fineCostModel` for arbitrary `messageKeys.length`:
`chainCloneTightCum ≤ 145,698 + 738 * messageKeys.length` (`2,214 + 143,484 = 145,698`). -/
theorem chainCloneTightCum_fine_le {gc : ChainGhost × ReceiverChain}
    (hsrk : gc.1.srk.bytes.length ≤ 44)
    (hpriv : gc.1.priv.bytes.length ≤ 44)
    (hseeds : ∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ 44) :
    chainCloneTightCum fineCostModel gc ≤ 145698 + 738 * gc.2.messageKeys.length := by
  unfold chainCloneTightCum
  have h1 := tryCloneSmallDelta_fine_le_738 hsrk
  have h2 := tryCloneSmallDelta_fine_le_738 hpriv
  have h3 : (match gc.2.chainKey with | none => 0 | some _ => rustAllocTightCum fineCostModel 32) ≤ 738 := by
    cases gc.2.chainKey with
    | none => exact Nat.zero_le 738
    | some _ => rw [rustAllocTightCum_fine_32]
  have h123 := Nat.add_le_add (Nat.add_le_add h1 h2) h3
  have h4 : (if gc.2.messageKeys = [] then 0
      else rustAllocTightCum fineCostModel (104 * gc.2.messageKeys.length) +
        (gc.2.messageKeys.map fun mkg => rustAllocTightCum fineCostModel mkg.seed.length).sum) ≤
      143484 + 738 * gc.2.messageKeys.length := by
    split
    · exact Nat.zero_le _
    · exact Nat.add_le_add
        (rustAllocTightCum_fine_le_143484 _)
        (list_map_sum_le_mul (fun mkg => rustAllocTightCum fineCostModel mkg.seed.length) 738
          gc.2.messageKeys (fun mkg hm => rustAllocTightCum_fine_le_738 (hseeds mkg hm)))
  have hcomb := Nat.add_le_add h123 h4
  have hrhs : (738 + 738 + 738) + (143484 + 738 * gc.2.messageKeys.length) =
      145698 + 738 * gc.2.messageKeys.length := by
    rw [← Nat.add_assoc ((738 + 738 + 738)), show (738 + 738 + 738) + 143484 = 145698 by decide]
  rw [hrhs] at hcomb
  exact hcomb

/-- Five-chain session `segCloneTightCum` bound (`≤ 1,500,446` B): at `st.receiverChains.length = 5`
with receiver-chain sum `≤ 1,487,192` B, `≤ 44`-B DJB keys, `0 ∨ 1569`-B Kyber ciphertext, and
`pq = 0 ∨ pq > 135,167`, `segCloneTightCum fineCostModel G st ≤ 1,500,446`. -/
theorem segCloneTightCum_fine_benchmark_le {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hloc : G.localIk.bytes.length ≤ 44)
    (hrem : G.remoteIk.bytes.length ≤ 44)
    (hsnd : ∀ gs sc, G.sender = some gs → st.senderChain = some sc →
      gs.srk.bytes.length ≤ 44 ∧ gs.priv.bytes.length ≤ 44)
    (hrc_len : st.receiverChains.length = 5)
    (hrc_sum : ((G.chains.zip st.receiverChains).map (chainCloneTightCum fineCostModel)).sum ≤ 1487192)
    (hpend : optTailCloneLen G.pending ≤ 44)
    (hkyb : optTailCloneLen G.kyber = 0 ∨ optTailCloneLen G.kyber = 1569)
    (halice : G.alice.bytes.length ≤ 44)
    (hpq : st.pqRatchetState.length = 0 ∨ 135167 < st.pqRatchetState.length) :
    segCloneTightCum fineCostModel G st ≤ 1500446 := by
  unfold segCloneTightCum
  have b1 := tryCloneSmallDelta_fine_le_738 hloc
  have b2 := tryCloneSmallDelta_fine_le_738 hrem
  have b3 : rustAllocTightCum fineCostModel 32 ≤ 738 := by
    rw [rustAllocTightCum_fine_32]
  have b4 : (match G.sender, st.senderChain with
      | some gs, some sc => chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc)
      | _, _ => 0) ≤ 2214 := by
    cases hs1 : G.sender <;> cases hs2 : st.senderChain
    · exact Nat.zero_le 2214
    · exact Nat.zero_le 2214
    · exact Nat.zero_le 2214
    · rename_i gs sc
      obtain ⟨hgs1, hgs2⟩ := hsnd gs sc hs1 hs2
      exact senderChainCloneTightCum_fine_le hgs1 hgs2
  have b5 : (if st.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * st.receiverChains.length) +
        ((G.chains.zip st.receiverChains).map (chainCloneTightCum fineCostModel)).sum) ≤ 1491628 := by
    have hne : st.receiverChains ≠ [] := by
      intro heq; rw [heq] at hrc_len; exact absurd hrc_len (by decide)
    simp only [hne, ↓reduceIte, hrc_len]
    have h520 : rustAllocTightCum fineCostModel (104 * 5) ≤ 4436 := by
      rw [show 104 * 5 = 520 by decide, rustAllocTightCum_fine_520]
    exact Nat.le_trans (Nat.add_le_add h520 hrc_sum) (by decide)
  have b6 := tryCloneSmallDelta_fine_le_738 hpend
  have b7 := tryCloneSmallDelta_fine_le_2792 hkyb
  have b8 := tryCloneSmallDelta_fine_le_738 halice
  have b9 := tryCloneSmallDelta_fine_pq_le_122 hpq
  exact Nat.le_trans
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add (Nat.add_le_add b1 b2) b3) b4) b5) b6) b7) b8) b9)
    (by decide)

private theorem add_nine_mid_aff_le
    {x1 x2 x3 x4 y x6 x7 x8 x9 b1 b2 b3 b4 bm b6 b7 b8 b9 total k : Nat}
    (h1 : x1 ≤ b1) (h2 : x2 ≤ b2) (h3 : x3 ≤ b3) (h4 : x4 ≤ b4)
    (hy : y ≤ bm + k)
    (h6 : x6 ≤ b6) (h7 : x7 ≤ b7) (h8 : x8 ≤ b8) (h9 : x9 ≤ b9)
    (hsum : b1 + b2 + b3 + b4 + bm + b6 + b7 + b8 + b9 ≤ total) :
    x1 + x2 + x3 + x4 + y + x6 + x7 + x8 + x9 ≤ total + k := by
  omega

/-- Domain-capped `segCloneTightCum` bound: for any session state with `≤ 5` receiver chains, total
skipped receiver keys `≤ maxKeys`, `≤ 44`-B DJB keys, `≤ 1,600`-B Kyber ciphertext, and arbitrary
`st.pqRatchetState.length`, `segCloneTightCum fineCostModel G st ≤ 891,173 + 738 * maxKeys`. -/
theorem segCloneTightCum_fine_univ_le {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    {maxKeys : Nat}
    (hloc : G.localIk.bytes.length ≤ 44)
    (hrem : G.remoteIk.bytes.length ≤ 44)
    (hsnd : ∀ gs sc, G.sender = some gs → st.senderChain = some sc →
      gs.srk.bytes.length ≤ 44 ∧ gs.priv.bytes.length ≤ 44)
    (hrc_len : st.receiverChains.length ≤ 5)
    (hrc_chains : ∀ gc ∈ G.chains.zip st.receiverChains,
      gc.1.srk.bytes.length ≤ 44 ∧ gc.1.priv.bytes.length ≤ 44 ∧
      (∀ mkg ∈ gc.2.messageKeys, mkg.seed.length ≤ 44))
    (hrc_keys : ((G.chains.zip st.receiverChains).map (fun gc => gc.2.messageKeys.length)).sum ≤ maxKeys)
    (hpend : optTailCloneLen G.pending ≤ 44)
    (hkyb : optTailCloneLen G.kyber = 0 ∨
      (1024 ≤ optTailCloneLen G.kyber ∧ optTailCloneLen G.kyber ≤ 1600))
    (halice : G.alice.bytes.length ≤ 44) :
    segCloneTightCum fineCostModel G st ≤ 891173 + 738 * maxKeys := by
  unfold segCloneTightCum
  have b1 := tryCloneSmallDelta_fine_le_738 hloc
  have b2 := tryCloneSmallDelta_fine_le_738 hrem
  have b3 : rustAllocTightCum fineCostModel 32 ≤ 738 := by
    rw [rustAllocTightCum_fine_32]
  have b4 : (match G.sender, st.senderChain with
      | some gs, some sc => chainCloneTightCum fineCostModel (senderChainAsProtoGhost gs sc)
      | _, _ => 0) ≤ 2214 := by
    cases hs1 : G.sender <;> cases hs2 : st.senderChain
    · exact Nat.zero_le 2214
    · exact Nat.zero_le 2214
    · exact Nat.zero_le 2214
    · rename_i gs sc
      obtain ⟨hgs1, hgs2⟩ := hsnd gs sc hs1 hs2
      exact senderChainCloneTightCum_fine_le hgs1 hgs2
  have b5 : (if st.receiverChains = [] then 0
      else rustAllocTightCum fineCostModel (104 * st.receiverChains.length) +
        ((G.chains.zip st.receiverChains).map (chainCloneTightCum fineCostModel)).sum) ≤
      738279 + 738 * maxKeys := by
    split
    · exact Nat.zero_le _
    · have hout : rustAllocTightCum fineCostModel (104 * st.receiverChains.length) ≤ 9789 := by
        unfold rustAllocTightCum
        have h520 : 104 * st.receiverChains.length ≤ 520 := by omega
        have hsm : 104 * st.receiverChains.length ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
          rw [fineCostModel_smallMaxReq_eq]
          exact Nat.le_trans h520 (by decide)
        simp only [hsm, ↓reduceIte]
        exact fineSmallAllocCost_le_9789_of_le_520 h520
      have hzip_len : (G.chains.zip st.receiverChains).length ≤ 5 := by
        rw [List.length_zip]
        exact Nat.le_trans (Nat.min_le_right _ _) hrc_len
      have haff := list_map_sum_aff_le
        (chainCloneTightCum fineCostModel) (fun gc => gc.2.messageKeys.length) 145698 738
        (G.chains.zip st.receiverChains)
        (fun gc hmem => by
          obtain ⟨hs, hp, hsd⟩ := hrc_chains gc hmem
          exact chainCloneTightCum_fine_le hs hp hsd)
      have h5mul : (G.chains.zip st.receiverChains).length * 145698 ≤ 728490 :=
        Nat.le_trans (Nat.mul_le_mul_right 145698 hzip_len) (by decide)
      have hk_mul : 738 * ((G.chains.zip st.receiverChains).map (fun gc => gc.2.messageKeys.length)).sum ≤
          738 * maxKeys :=
        Nat.mul_le_mul_left 738 hrc_keys
      have hsum_le : ((G.chains.zip st.receiverChains).map (chainCloneTightCum fineCostModel)).sum ≤
          728490 + 738 * maxKeys :=
        Nat.le_trans haff (Nat.add_le_add h5mul hk_mul)
      have htot := Nat.add_le_add hout hsum_le
      have hrhs : 9789 + (728490 + 738 * maxKeys) = 738279 + 738 * maxKeys := by
        rw [← Nat.add_assoc 9789, show 9789 + 728490 = 738279 by decide]
      rw [hrhs] at htot
      exact htot
  have b6 := tryCloneSmallDelta_fine_le_738 hpend
  have b7 := tryCloneSmallDelta_fine_kyber_range_le_3506 hkyb
  have b8 := tryCloneSmallDelta_fine_le_738 halice
  have b9 := tryCloneSmallDelta_fine_le_143484 st.pqRatchetState.length
  exact add_nine_mid_aff_le b1 b2 b3 b4 b5 b6 b7 b8 b9 (by decide)

end TightCloneCredit

end LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
