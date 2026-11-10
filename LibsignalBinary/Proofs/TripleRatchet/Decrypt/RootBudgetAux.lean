/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitEvict
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root

/-!
# Seam Event Envelopes & Precondition Helpers for `RootBudget`

Defines `TrGhostCaps` capacity profiles, remaining-events seam envelopes (`FromS8GenEnv` ..
`FromS1GenEnv`, specialized to standard and `decFn` variants), envelope inhabitedness lemmas, and
budget-form precondition/panic helpers for `RootBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  ChainKey Crypto MessageKeyGenerator MessageKeys Mut RatchetState
  SessionState SignalMessage SignalProtocolError TripleRatchet aesCbcDecrypt
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalSessionRepr (ChainGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost UuidParser coinsOf decryptDraws serializeAddresses serviceIdParse uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SeedsLen32 SpqrModel TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit (evictList)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ConsumeMsgKeyStatePlaced DhStepStatePlaced ErrTailStatePlaced
  FindChainStatePlaced LoadRatchetStatePlaced
  tryDecryptFnOnPanic tryDecryptFnSpecPlaced
  tryDecryptOnPanic tryDecryptRawSpecPlaced tryDecryptSpecPlaced
)

/-! ## 1. Remaining-Events Seam Envelopes & Inhabitedness -/

/-- Capacity profile of a `TrGhost`: `receiver_chains` buffer capacity, per-chain
    `message_keys` buffer capacities, and `pqr_state` buffer capacity. -/
structure TrGhostCaps where
  chainsCap : BitVec 64
  mkCaps : List (BitVec 64)
  pqCap : BitVec 64
  deriving DecidableEq

/-- Extract the allocation-relevant capacity profile of `trG`. -/
def trGhostCaps (trG : TrGhost) : TrGhostCaps where
  chainsCap := trG.ratchet.chainsCap
  mkCaps := trG.ratchet.chains.map ChainGhost.mkCap
  pqCap := trG.pq.cap

/-- Canonical `ChainGhost` representative for a given `mkCap`. -/
def dummyChainOfMkCap (mkCap : BitVec 64) : ChainGhost where
  srk := ⟨33#64, 1#64, []⟩
  priv := ⟨0#64, 1#64, []⟩
  mkCap := mkCap
  mkPtr := 8#64
  keys := []
  ck := ⟨32#64, 1#64⟩

/-- Canonical `TrGhost` representative realizing capacity profile `c`. -/
def trGhostOfCaps (c : TrGhostCaps) : TrGhost where
  ratchet :=
    { chainsCap := c.chainsCap
      chainsPtr := 8#64
      chains := c.mkCaps.map dummyChainOfMkCap
      senderPad := List.replicate 100 0#8 }
  pq := ⟨c.pqCap, 1#64⟩

theorem caps_trGhostOfCaps (c : TrGhostCaps) : trGhostCaps (trGhostOfCaps c) = c := by
  cases c with | mk cc mc pc =>
  simp [trGhostCaps, trGhostOfCaps, List.map_map, Function.comp_def, dummyChainOfMkCap]

/-- Deterministic post-`S1` (`from_session_state`) capacity profile moved from `G`. -/
def s1InitCaps (G : SessionGhost) : TrGhostCaps where
  chainsCap := G.chainsCap
  mkCaps := G.chains.map ChainGhost.mkCap
  pqCap := G.pq.cap

/-- Deterministic post-`S3` (`dh_ratchet_step`) `receiver_chains` buffer capacity. -/
def dhStepNewChainsCap (chainsCap : BitVec 64) (rcLen : Nat) : BitVec 64 :=
  if BitVec.ofNat 64 rcLen = chainsCap then
    BitVec.ofNat 64 (max (2 * chainsCap.toNat) 4)
  else
    chainsCap

/-- Deterministic post-`S3` (`dh_ratchet_step`) capacity profile after optional `grow_one`,
    pushing a fresh receiver chain (`mkCap = 0#64`), and evicting beyond `maxReceiverChains`. -/
def s3AfterCaps (c : TrGhostCaps) (rcLen : Nat) : TrGhostCaps where
  chainsCap := dhStepNewChainsCap c.chainsCap rcLen
  mkCaps := evictList (c.mkCaps ++ [0#64])
  pqCap := c.pqCap

/-- Canonical deterministic `TrGhost` at `S2` entry derived from pre-state `G`. -/
def s1InitTrGhost (G : SessionGhost) : TrGhost :=
  trGhostOfCaps (s1InitCaps G)

/-- Canonical deterministic `TrGhost` at `S4` entry after `S3` (`dh_ratchet_step`). -/
def s3AfterTrGhost (trG : TrGhost) (rcLen : Nat) : TrGhost :=
  trGhostOfCaps (s3AfterCaps (trGhostCaps trG) rcLen)

theorem freeOnlyEvs_nil : FreeOnlyEvs [] := by
  simp [FreeOnlyEvs]

theorem seqEnv_append {E₁ E₂ : List AllocEvent → Prop} {e₁ e₂ : List AllocEvent}
    (h1 : E₁ e₁) (h2 : E₂ e₂) : SeqEnv E₁ E₂ (e₁ ++ e₂) :=
  Or.inr ⟨e₁, e₂, rfl, h1, h2⟩

theorem seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ e, E₁ e → E₁' e) (h2 : ∀ e, E₂ e → E₂' e)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) : SeqEnv E₁' E₂' evs := by
  rcases h with h | ⟨e₁, e₂, rfl, he₁, he₂⟩
  · exact Or.inl (h1 evs h)
  · exact Or.inr ⟨e₁, e₂, rfl, h1 e₁ he₁, h2 e₂ he₂⟩

theorem seqEnv_ne {E₁ E₂ : List AllocEvent → Prop}
    (h1 : ∃ e₁, E₁ e₁) (h2 : ∃ e₂, E₂ e₂) : ∃ evs, SeqEnv E₁ E₂ evs := by
  rcases h1 with ⟨e₁, he₁⟩
  rcases h2 with ⟨e₂, he₂⟩
  exact ⟨e₁ ++ e₂, seqEnv_append he₁ he₂⟩

/-- Inhabitedness and ghost-capacity invariance of segment envelopes `s4..s9`
    (sufficient for `reaches_outcome_of_s4*_placed`). -/
structure FromS4EnvsInhabited
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  s4 : ∀ x trG tr ck, ∃ evs, s4Env x trG tr ck evs
  s5 : ∀ x tr, ∃ evs, s5Env x tr evs
  s6 : ∀ mkg, ∃ evs, s6Env mkg evs
  s7 : ∀ x tr mks newPqrState, ∃ evs, s7Env x tr mks newPqrState evs
  s8 : ∀ x mks newPqrState, ∃ evs, s8Env x mks newPqrState evs
  s9 : ∀ x trG tr st1 newPqrState, ∃ evs, s9Env x trG tr st1 newPqrState evs
  s4_caps : ∀ x trG₁ trG₂ tr ck evs,
    trGhostCaps trG₁ = trGhostCaps trG₂ → s4Env x trG₁ tr ck evs → s4Env x trG₂ tr ck evs
  s9_trG : ∀ x trG₁ trG₂ tr st1 newPqrState evs,
    s9Env x trG₁ tr st1 newPqrState evs → s9Env x trG₂ tr st1 newPqrState evs

/-- Inhabitedness and ghost-capacity invariance of segment envelopes `s3..s9`
    (sufficient for `try_decrypt_placed_ok_of_seams*`). -/
structure SeamEnvsInhabited
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) : Prop extends
    FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env where
  s3 : ∀ x trG tr, ∃ evs, s3Env x trG tr evs
  s3_caps : ∀ x trG₁ trG₂ tr evs,
    trGhostCaps trG₁ = trGhostCaps trG₂ → s3Env x trG₁ tr evs → s3Env x trG₂ tr evs

/-- Pinned `S1` (`LoadRatchet`) seam contract recording `trGhostCaps trG = s1InitCaps x.G`. -/
def S1SeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
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
      reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

/-- Pinned `S3` (`DhStep`) seam contract recording
    `trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length`. -/
def S3SeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
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
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

/-- Pinned `decFn` (`X`) `S1` (`LoadRatchet`) seam contract recording `trGhostCaps trG = s1InitCaps x.G`. -/
def S1SeamPinnedXPlaced [LibsignalPlacement] {M : AllocCostModel}
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
      reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

/-- Pinned `decFn` (`X`) `S3` (`DhStep`) seam contract recording
    `trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length`. -/
def S3SeamPinnedXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) :
    Prop :=
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
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

def FromS8GenEnv
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys) (newPqrState : List (BitVec 8)) :
    List AllocEvent → Prop :=
  match aesOpt mks x.msg with
  | some _ => SeqEnv (s8Env x mks newPqrState) (s9Env x trG tr st1 newPqrState)
  | none => SeqEnv (s8Env x mks newPqrState) FreeOnlyEvs

def FromS7GenEnv (C : Crypto) (parse : UuidParser)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys) (newPqrState : List (BitVec 8)) :
    List AllocEvent → Prop :=
  if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
      tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
    SeqEnv (s7Env x tr mks newPqrState)
      (FromS8GenEnv aesOpt s8Env s9Env x trG tr st1 mks newPqrState)
  else
    SeqEnv (s7Env x tr mks newPqrState) FreeOnlyEvs

def FromS6GenEnv (C : Crypto) (parse : UuidParser)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) :
    List AllocEvent → Prop :=
  SeqEnv (s6Env mkg)
    (FromS7GenEnv C parse aesOpt s7Env s8Env s9Env
      x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState)

def FromS5GenEnv (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) :
    List AllocEvent → Prop :=
  match S.recv tr.pqrState x.msg.pqRatchet with
  | .ok (newPqrState, pqrKey) =>
    SeqEnv (s5Env x tr)
      (FromS6GenEnv C parse aesOpt s6Env s7Env s8Env s9Env x trG tr st1 mkg newPqrState pqrKey)
  | .error _ =>
    SeqEnv (s5Env x tr) FreeOnlyEvs

def FromS4GenEnv (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) :
    List AllocEvent → Prop :=
  match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) tr.ratchet with
  | (.ok mkg, r2) =>
    SeqEnv (s4Env x trG tr ck)
      (FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env s8Env s9Env
        x trG { tr with ratchet := r2 } st1 mkg)
  | (.error _, _) =>
    SeqEnv (s4Env x trG tr ck) FreeOnlyEvs

def FromS3GenEnv (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
      (coinsOf x.rest)) tr.ratchet with
  | (.ok ck, r1) =>
    SeqEnv (s3Env x trG tr)
      (FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env
        x (s3AfterTrGhost trG tr.ratchet.receiverChains.length)
        { tr with ratchet := r1 } st1 ck)
  | (.error _, _) =>
    SeqEnv (s3Env x trG tr) FreeOnlyEvs

def FromS2GenEnv (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | .ok (some ck) =>
    FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1 ck
  | .ok none =>
    FromS3GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1
  | .error _ =>
    FreeOnlyEvs

/-- Full seam-composed allocator event envelope from `S1` (`LoadRatchet`) parameterized by `aesOpt`. -/
def FromS1GenEnv (C : Crypto) (parse : UuidParser) (S : SpqrModel)
    (aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8)))
    (s1OkEnv : TryDecryptGhost → List AllocEvent → Prop)
    (s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop)
    (x : TryDecryptGhost) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState x.st with
  | (.error _, _) => fun evs => evs = []
  | (.ok tr0, st1) =>
    SeqEnv (s1OkEnv x)
      (FromS2GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
        x (s1InitTrGhost x.G) tr0 st1)

/-- Standard `aesCbcDecrypt` selector for `FromS8GenEnv` .. `FromS1GenEnv`. -/
def stdAesOpt (C : Crypto) (mks : MessageKeys) (msg : SignalMessage) : Option (List (BitVec 8)) :=
  aesCbcDecrypt C.D mks.cipherKey mks.iv msg.ciphertext

/-- `decFn` selector for `FromS8GenEnv` .. `FromS1GenEnv`. -/
def fnAesOpt (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (mks : MessageKeys) (msg : SignalMessage) : Option (List (BitVec 8)) :=
  decFn msg.ciphertext (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv)

abbrev FromS4Env (C : Crypto) (parse : UuidParser) (S : SpqrModel) :=
  FromS4GenEnv C parse S (stdAesOpt C)

abbrev FromS1Env (C : Crypto) (parse : UuidParser) (S : SpqrModel) :=
  FromS1GenEnv C parse S (stdAesOpt C)

abbrev FromS4FnEnv (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (parse : UuidParser) (S : SpqrModel) :=
  FromS4GenEnv C parse S (fnAesOpt decFn)

abbrev FromS1FnEnv (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (parse : UuidParser) (S : SpqrModel) :=
  FromS1GenEnv C parse S (fnAesOpt decFn)

section InhabitedLemmas

variable {C : Crypto} {parse : UuidParser} {S : SpqrModel}
  {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
  {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
    List AllocEvent → Prop}
  {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
  {s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
    List (BitVec 8) → List AllocEvent → Prop}
  {s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
  {s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
    SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}

theorem fromS8GenEnv_ne
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys) (newPqrState : List (BitVec 8)) :
    ∃ evs, FromS8GenEnv aesOpt s8Env s9Env x trG tr st1 mks newPqrState evs := by
  unfold FromS8GenEnv
  cases aesOpt mks x.msg with
  | none => exact seqEnv_ne (hne.s8 x mks newPqrState) ⟨[], freeOnlyEvs_nil⟩
  | some _ => exact seqEnv_ne (hne.s8 x mks newPqrState) (hne.s9 x trG tr st1 newPqrState)

theorem fromS7GenEnv_ne
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys) (newPqrState : List (BitVec 8)) :
    ∃ evs, FromS7GenEnv C parse aesOpt s7Env s8Env s9Env x trG tr st1 mks newPqrState evs := by
  unfold FromS7GenEnv
  split
  · exact seqEnv_ne (hne.s7 x tr mks newPqrState)
      (fromS8GenEnv_ne hne x trG tr st1 mks newPqrState)
  · exact seqEnv_ne (hne.s7 x tr mks newPqrState) ⟨[], freeOnlyEvs_nil⟩

theorem fromS6GenEnv_ne
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) :
    ∃ evs, FromS6GenEnv C parse aesOpt s6Env s7Env s8Env s9Env
      x trG tr st1 mkg newPqrState pqrKey evs :=
  seqEnv_ne (hne.s6 mkg)
    (fromS7GenEnv_ne hne x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState)

theorem fromS5GenEnv_ne
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) :
    ∃ evs, FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env s8Env s9Env x trG tr st1 mkg evs := by
  unfold FromS5GenEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | error _ => exact seqEnv_ne (hne.s5 x tr) ⟨[], freeOnlyEvs_nil⟩
  | ok pqrRes =>
    rcases pqrRes with ⟨newPqrState, pqrKey⟩
    exact seqEnv_ne (hne.s5 x tr)
      (fromS6GenEnv_ne hne x trG tr st1 mkg newPqrState pqrKey)

theorem fromS4GenEnv_ne
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) :
    ∃ evs, FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env x trG tr st1 ck evs := by
  unfold FromS4GenEnv
  cases Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) tr.ratchet with
  | mk res r2 =>
    cases res with
    | error _ => exact seqEnv_ne (hne.s4 x trG tr ck) ⟨[], freeOnlyEvs_nil⟩
    | ok mkg =>
      exact seqEnv_ne (hne.s4 x trG tr ck)
        (fromS5GenEnv_ne (C := C) (parse := parse) (S := S) (aesOpt := aesOpt)
          hne x trG { tr with ratchet := r2 } st1 mkg)

theorem fromS3GenEnv_ne
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) :
    ∃ evs, FromS3GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG tr st1 evs := by
  unfold FromS3GenEnv
  cases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
      (coinsOf x.rest)) tr.ratchet with
  | mk res r1 =>
    cases res with
    | error _ => exact seqEnv_ne (hne.s3 x trG tr) ⟨[], freeOnlyEvs_nil⟩
    | ok ck =>
      exact seqEnv_ne (hne.s3 x trG tr)
        (fromS4GenEnv_ne (C := C) (parse := parse) (S := S) (aesOpt := aesOpt)
          hne.toFromS4EnvsInhabited
          x (s3AfterTrGhost trG tr.ratchet.receiverChains.length)
          { tr with ratchet := r1 } st1 ck)

theorem fromS2GenEnv_ne
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) :
    ∃ evs, FromS2GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG tr st1 evs := by
  unfold FromS2GenEnv
  cases tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | error _ => exact ⟨[], freeOnlyEvs_nil⟩
  | ok optCk =>
    cases optCk with
    | some ck =>
      exact fromS4GenEnv_ne hne.toFromS4EnvsInhabited x trG tr st1 ck
    | none =>
      exact fromS3GenEnv_ne hne x trG tr st1

theorem fromS8GenEnv_trG
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqrState : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : FromS8GenEnv aesOpt s8Env s9Env x trG₁ tr st1 mks newPqrState evs) :
    FromS8GenEnv aesOpt s8Env s9Env x trG₂ tr st1 mks newPqrState evs := by
  revert h
  unfold FromS8GenEnv
  cases aesOpt mks x.msg with
  | none => exact fun h => h
  | some _ =>
    exact fun h => seqEnv_mono (fun _ he => he) (hne.s9_trG x trG₁ trG₂ tr st1 newPqrState) h

theorem fromS7GenEnv_trG
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqrState : List (BitVec 8)}
    {evs : List AllocEvent}
    (h : FromS7GenEnv C parse aesOpt s7Env s8Env s9Env x trG₁ tr st1 mks newPqrState evs) :
    FromS7GenEnv C parse aesOpt s7Env s8Env s9Env x trG₂ tr st1 mks newPqrState evs := by
  revert h
  unfold FromS7GenEnv
  split
  · exact fun h => seqEnv_mono (fun _ he => he) (fun _ he => fromS8GenEnv_trG hne he) h
  · exact fun h => h

theorem fromS6GenEnv_trG
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    {newPqrState : List (BitVec 8)} {pqrKey : Salt} {evs : List AllocEvent}
    (h : FromS6GenEnv C parse aesOpt s6Env s7Env s8Env s9Env
      x trG₁ tr st1 mkg newPqrState pqrKey evs) :
    FromS6GenEnv C parse aesOpt s6Env s7Env s8Env s9Env
      x trG₂ tr st1 mkg newPqrState pqrKey evs :=
  seqEnv_mono (fun _ he => he) (fun _ he => fromS7GenEnv_trG hne he) h

theorem fromS5GenEnv_trG
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator} {evs : List AllocEvent}
    (h : FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env s8Env s9Env x trG₁ tr st1 mkg evs) :
    FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env s8Env s9Env x trG₂ tr st1 mkg evs := by
  revert h
  unfold FromS5GenEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | error _ => exact fun h => h
  | ok pqrRes =>
    rcases pqrRes with ⟨newPqrState, pqrKey⟩
    exact fun h => seqEnv_mono (fun _ he => he) (fun _ he => fromS6GenEnv_trG hne he) h

theorem fromS4GenEnv_caps
    (hne : FromS4EnvsInhabited s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {evs : List AllocEvent}
    (hcaps : trGhostCaps trG₁ = trGhostCaps trG₂)
    (h : FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env x trG₁ tr st1 ck evs) :
    FromS4GenEnv C parse S aesOpt s4Env s5Env s6Env s7Env s8Env s9Env x trG₂ tr st1 ck evs := by
  revert h
  unfold FromS4GenEnv
  cases Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) tr.ratchet with
  | mk res r2 =>
    cases res with
    | error _ =>
      exact fun h => seqEnv_mono (fun e => hne.s4_caps x trG₁ trG₂ tr ck e hcaps) (fun _ he => he) h
    | ok mkg =>
      exact fun h => seqEnv_mono (fun e => hne.s4_caps x trG₁ trG₂ tr ck e hcaps)
        (fun _ he => fromS5GenEnv_trG hne he) h

theorem fromS3GenEnv_caps
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {evs : List AllocEvent}
    (hcaps : trGhostCaps trG₁ = trGhostCaps trG₂)
    (h : FromS3GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG₁ tr st1 evs) :
    FromS3GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG₂ tr st1 evs := by
  revert h
  unfold FromS3GenEnv
  cases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
      (coinsOf x.rest)) tr.ratchet with
  | mk res r1 =>
    cases res with
    | error _ =>
      exact fun h => seqEnv_mono (fun e => hne.s3_caps x trG₁ trG₂ tr e hcaps) (fun _ he => he) h
    | ok ck =>
      have hs3_eq : s3AfterTrGhost trG₁ tr.ratchet.receiverChains.length =
          s3AfterTrGhost trG₂ tr.ratchet.receiverChains.length := by
        unfold s3AfterTrGhost; rw [hcaps]
      exact fun h => seqEnv_mono (fun e => hne.s3_caps x trG₁ trG₂ tr e hcaps)
        (fun _ he => hs3_eq ▸ he) h

theorem fromS2GenEnv_caps
    (hne : SeamEnvsInhabited s3Env s4Env s5Env s6Env s7Env s8Env s9Env)
    {x : TryDecryptGhost} {trG₁ trG₂ : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {evs : List AllocEvent}
    (hcaps : trGhostCaps trG₁ = trGhostCaps trG₂)
    (h : FromS2GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG₁ tr st1 evs) :
    FromS2GenEnv C parse S aesOpt s3Env s4Env s5Env s6Env s7Env s8Env s9Env
      x trG₂ tr st1 evs := by
  revert h
  unfold FromS2GenEnv
  cases tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | error _ => exact fun h => h
  | ok optCk =>
    cases optCk with
    | some ck =>
      exact fun h => fromS4GenEnv_caps hne.toFromS4EnvsInhabited hcaps h
    | none =>
      exact fun h => fromS3GenEnv_caps hne hcaps h

end InhabitedLemmas

/-! ## 2. Budget-Form Precondition Extraction & Panic Outcome Helpers -/

private theorem rawPre_unbudget_of_pre_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) :
    FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) ∧
      (s0.mem ⊨
        (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptSpecPlaced
          C (A.atState lim st_init s0) ctl parse S).pre x s0 ∗ R) := by
  dsimp only [tryDecryptSpecPlaced,
    CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptSpecPlaced,
    withLsCodeRoLoaded, tryDecryptRawSpecPlaced] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre ⊢
  rcases hpre with ⟨hcl, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨hpre.1, hcl, hpre.2⟩

theorem fitsEnv_of_pre_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) :
    FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) :=
  (rawPre_unbudget_of_pre_placed hpre).1

theorem seedsLen32_of_pre_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.seedsLen32_of_pre_placed
    (rawPre_unbudget_of_pre_placed hpre).2

theorem restLen_of_pre_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptSpecPlaced C A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    x.rest.length < 2 ^ 63 :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.restLen_of_pre_placed
    (rawPre_unbudget_of_pre_placed hpre).2

theorem reaches_outcome_of_panic_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R) :
    reaches_outcome P (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s :=
  Arm64.reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan hq)

theorem onPanic_of_cmk_panic_placed {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S parse).1 = .error e)
    (hp : e = .panic ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R := by
  rcases hp with ⟨rfl, htr⟩
  unfold tryDecryptOnPanic
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨Or.inl hm1, htr⟩, hmem⟩

theorem tryDecryptFnSpecPlaced_pre_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).pre =
      (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).pre :=
  rfl

theorem fitsEnv_of_pre_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) :
    FitsEnv M lim st_init (tdEnv (tryDecryptEnvArgs x)) := by
  rw [tryDecryptFnSpecPlaced_pre_eq] at hpre
  exact fitsEnv_of_pre_placed hpre

theorem seedsLen32_of_pre_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  rw [tryDecryptFnSpecPlaced_pre_eq] at hpre
  exact seedsLen32_of_pre_placed hpre

theorem restLen_of_pre_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl uuidTryParse S tdEnv).pre (x, st_init) s0 ∗ R) :
    x.rest.length < 2 ^ 63 := by
  rw [tryDecryptFnSpecPlaced_pre_eq] at hpre
  exact restLen_of_pre_placed hpre

theorem reaches_outcome_of_panic_fn_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R) :
    reaches_outcome P (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s :=
  Arm64.reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan hq)

theorem onPanic_of_cmk_panic_fn_placed {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {parse : UuidParser} {S : SpqrModel}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.modelFn C decFn S parse).1 = .error e)
    (hp : e = .panic ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R := by
  rcases hp with ⟨rfl, htr⟩
  unfold tryDecryptFnOnPanic
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨Or.inl hm1, htr⟩, hmem⟩

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
