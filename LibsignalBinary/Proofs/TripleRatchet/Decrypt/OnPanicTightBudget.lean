/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight

/-!
# Budget-Threaded Tight Panic Contracts for `try_decrypt_with_state`

Defines `tryDecryptOnPanicTight` and `tryDecryptFnOnPanicTight` over `RustCliAllocBudget M`
(dropping both `S.recvPanics` and `allocFailedIn`, retaining only model panics), together with
`ErrTailSeamTightPlaced`, `S1SeamTightPlaced`, `S3SeamTightPlaced`, their `decFn` (`X`) variants,
and `.weaken` bridges to `DefsBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto Mut RatchetState SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser coinsOf decryptDraws)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ErrTailStatePlaced ErrTailStateXPlaced LoadRatchetStatePlaced FindChainStatePlaced
  ConsumeMsgKeyStatePlaced DhStepStatePlaced
  tryDecryptOnPanic tryDecryptFnOnPanic
  tryDecryptRawSpecPlaced tryDecryptSpecPlaced
  tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
  ErrTailSeamPlaced S1SeamPlaced S3SeamPlaced
  ErrTailSeamXPlaced S1SeamXPlaced S3SeamXPlaced
)

/-! ## 1. Standard Tight Panic Contracts & Seams -/

/-- Budget-threaded tight panic postcondition for `try_decrypt_with_state`: drops both
    `S.recvPanics` and `allocFailedIn`, keeping only `(x.model C S parse).1 = .error .panic`
    and trace monotonicity. -/
def tryDecryptOnPanicTight (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (x : TryDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜(x.model C S parse).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Tight panic condition implies `DefsBudget.tryDecryptOnPanic`. -/
theorem tryDecryptOnPanicTight_weaken {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanic C parse S x s0 sf ∗ R := by
  simp only [tryDecryptOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanic]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hp, htr⟩, hmem⟩ := h
  exact ⟨⟨Or.inl hp, htr⟩, hmem⟩

/-- `DefsBudget.tryDecryptRawSpecPlaced` with tight `onPanic := tryDecryptOnPanicTight`. -/
def tryDecryptRawSpecTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { tryDecryptRawSpecPlaced C A lim ctl parse S tdEnv with
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S parse x s0 sf }

/-- `DefsBudget.tryDecryptSpecPlaced` with tight `onPanic := tryDecryptOnPanicTight`. -/
def tryDecryptSpecTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (tryDecryptRawSpecTightPlaced C A lim ctl parse S tdEnv)

theorem tryDecryptOnPanicTight_weaken_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic
      (x, st_init) s0 sf ∗ R := by
  simp only [tryDecryptSpecPlaced, withLsCodeRoLoaded, tryDecryptRawSpecPlaced]
  exact tryDecryptOnPanicTight_weaken h

theorem reaches_outcome_tight_weaken_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (tryDecryptSpecTightPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s) :
    reaches_outcome P (tryDecryptSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptOnPanicTight_weaken_placed hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

def ErrTailSeamTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S parse).1 = .error e →
    (x.model C S parse).2 = st1 →
    SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs →
    ErrTailStatePlaced entry A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptSpecTightPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

def S1SeamTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st (fun evs => evs = []) →
      reaches_outcome prog (tryDecryptSpecTightPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

def S3SeamTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
        (coinsOf x.rest)) tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG', s3Env x trG tr evs ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

theorem ErrTailSeamTightPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h : ErrTailSeamTightPlaced prog entry C A lim ctl parse S tdEnv) :
    ErrTailSeamPlaced prog entry C A lim ctl parse S tdEnv :=
  fun x st_init st trG tr st1 e R s0 s hne hm1 hm2 hsb hst =>
    reaches_outcome_tight_weaken_placed (h x st_init st trG tr st1 e R s0 s hne hm1 hm2 hsb hst)

theorem S1SeamTightPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (h : S1SeamTightPlaced prog entry C A lim ctl parse S tdEnv s1OkEnv) :
    S1SeamPlaced prog entry C A lim ctl parse S tdEnv s1OkEnv := by
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact fun hfn hsb => reaches_outcome_tight_weaken_placed (hfn hsb)
  · exact id

theorem S3SeamTightPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : S3SeamTightPlaced prog entry C A lim ctl parse S s3Env) :
    S3SeamPlaced prog entry C A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  have h' := h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  dsimp only at h' ⊢
  revert h'
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with ⟨_ | ck, r1⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

/-! ## 2. `Stage2ContractsX` (`decFn` / `X`) Tight Panic Contracts & Seams -/

/-- Budget-threaded tight panic postcondition for `tryDecryptFnSpecPlaced` (`decFn` variant). -/
def tryDecryptFnOnPanicTight (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (parse : UuidParser)
    (x : TryDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜(x.modelFn C decFn S parse).1 = .error .panic ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Tight `decFn` panic condition implies `DefsBudget.tryDecryptFnOnPanic`. -/
theorem tryDecryptFnOnPanicTight_weaken {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptFnOnPanicTight C decFn S parse x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 sf ∗ R := by
  simp only [tryDecryptFnOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptFnOnPanic]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hp, htr⟩, hmem⟩ := h
  exact ⟨⟨Or.inl hp, htr⟩, hmem⟩

def tryDecryptFnRawSpecTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  { tryDecryptFnRawSpecPlaced C decFn A lim ctl parse S tdEnv with
    onPanic := fun (x, _) s0 sf => tryDecryptFnOnPanicTight C decFn S parse x s0 sf }

def tryDecryptFnSpecTightPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (tryDecryptFnRawSpecTightPlaced C decFn A lim ctl parse S tdEnv)

theorem tryDecryptFnOnPanicTight_weaken_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptFnOnPanicTight C decFn S parse x s0 sf ∗ R) :
    sf.mem ⊨ (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic
      (x, st_init) s0 sf ∗ R := by
  simp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded, tryDecryptFnRawSpecPlaced]
  exact tryDecryptFnOnPanicTight_weaken h

theorem reaches_outcome_fn_tight_weaken_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (tryDecryptFnSpecTightPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s) :
    reaches_outcome P (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptFnOnPanicTight_weaken_placed hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

def ErrTailSeamTightXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.modelFn C decFn S parse).1 = .error e →
    (x.modelFn C decFn S parse).2 = st1 →
    SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st FreeOnlyEvs →
    ErrTailStateXPlaced entry A lim st ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptFnSpecTightPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

def S1SeamTightXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A lim st ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st (fun evs => evs = []) →
      reaches_outcome prog (tryDecryptFnSpecTightPlaced C decFn A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

def S3SeamTightXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    FitsEnv M lim st (s3Env x trG tr) →
    DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
        (coinsOf x.rest)) tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG', s3Env x trG tr evs ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanicTight C decFn S parse x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanicTight C decFn S parse x s0 s' ∗ R)))

theorem ErrTailSeamTightXPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h : ErrTailSeamTightXPlaced prog entry C decFn A lim ctl parse S tdEnv) :
    ErrTailSeamXPlaced prog entry C decFn A lim ctl parse S tdEnv :=
  fun x st_init st trG tr st1 e R s0 s hne hm1 hm2 hsb hst =>
    reaches_outcome_fn_tight_weaken_placed
      (h x st_init st trG tr st1 e R s0 s hne hm1 hm2 hsb hst)

theorem S1SeamTightXPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (h : S1SeamTightXPlaced prog entry C decFn A lim ctl parse S tdEnv s1OkEnv) :
    S1SeamXPlaced prog entry C decFn A lim ctl parse S tdEnv s1OkEnv := by
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact fun hfn hsb => reaches_outcome_fn_tight_weaken_placed (hfn hsb)
  · exact id

theorem S3SeamTightXPlaced.weaken [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : S3SeamTightXPlaced prog entry C decFn A lim ctl parse S s3Env) :
    S3SeamXPlaced prog entry C decFn A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  have h' := h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  dsimp only at h' ⊢
  revert h'
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with ⟨_ | ck, r1⟩
  · rintro ⟨s', hok, hbranch⟩
    rcases hbranch with hok' | ⟨hpan, hq⟩
    · exact ⟨s', hok, Or.inl hok'⟩
    · exact ⟨s', hok, Or.inr ⟨hpan, tryDecryptFnOnPanicTight_weaken hq⟩⟩
  · rintro ⟨s', hok, hbranch⟩
    rcases hbranch with hok' | ⟨hpan, hq⟩
    · exact ⟨s', hok, Or.inl hok'⟩
    · exact ⟨s', hok, Or.inr ⟨hpan, tryDecryptFnOnPanicTight_weaken hq⟩⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
