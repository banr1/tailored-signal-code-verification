/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.CorePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux

/-!
# Budget-Threaded Relocatable Checkpoints and Seams for `try_decrypt_with_state::<Coins>`

Threads allocator cost-model state (`RustCliAllocBudget M`) and per-segment allocator event
envelopes (`SeamBudget`) across the relocatable checkpoint states, whole-function contracts, and
segment seams of `try_decrypt_with_state::<Coins>` (block `433`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  ChainKey Crypto MessageKeyGenerator MessageKeys Mut RatchetState
  SessionState SignalProtocolError TripleRatchet aesCbcDecrypt
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws serializeAddresses serviceIdParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPl_434 errTailPC_at segConsumeMsgKeyPC_at segDhStepPC_at
  segLoadRatchetPC_at segVerifyMacPC_at
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (tryDecryptOnPanic)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (
  tryDecryptOnPanicTight tryDecryptOnPanicTight_weaken
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux (
  s1InitCaps s3AfterCaps trGhostCaps
)

/-! ## Budget-Threaded Common Heap and Checkpoint States -/

theorem blk433_base_eq [LibsignalPlacement] : (blkPl_434).base = lsmpl.base 434 := rfl

/-- Budget-threaded relocatable `[LibsignalPlacement]` CLI common heap invariant across Block `433`
checkpoints, threading `A.atState lim st s`. -/
def cliTryDecryptCommonHeapPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (ctl : BitVec 64)
    (x : TryDecryptGhost) (draws : Nat) (s0 s : State) : SepProp :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.cliTryDecryptCommonHeapPlaced
    (A.atState lim st s) ctl x draws s0

def ErrTailStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

def LoadRatchetStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetStatePlaced
    entry (A.atState lim st s) ctl x R s0 s

def FindChainStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.FindChainStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 R s0 s

def DhStepStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 R s0 s

def ConsumeMsgKeyStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (ck : ChainKey) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 ck draws R s0 s

def PqRecvStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.PqRecvStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mkg draws R s0 s

def DeriveKeysStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (newPqrState : List (BitVec 8)) (pqrKey : Salt)
    (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DeriveKeysStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s

def VerifyMacStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.VerifyMacStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mks newPqrState draws R s0 s

def AesDecryptStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.AesDecryptStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mks newPqrState draws R s0 s

def ApplyRatchetStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ApplyRatchetStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 newPqrState pt draws R s0 s

/-! ## Budget-Threaded Whole-Function `try_decrypt_with_state` Contracts -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` tight-panic `try_decrypt_with_state` spec
with `SpqrV1.GF.Mul2U16.tokenInitPlacedAt` framed and `DistinctSid`-weakened identity guard
(raw, before `withLsCodeRoLoaded lsmpl`). -/
abbrev tryDecryptRawSpecTPTightAt [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget.tryDecryptPlacedSpecQF_PTight
    (·.length < 2 ^ 32) tokenInitPlacedAt C A lim ctl uuidParse S tdEnv

def tryDecryptSpecTPTightAt [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (tryDecryptRawSpecTPTightAt C A lim ctl uuidParse S tdEnv)

def cliTryDecryptSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget.tryDecryptPlacedSpec
      C A lim ctl uuidParse S tdEnv)

def cliTryDecryptTightSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget.tryDecryptPlacedTightSpec
      C A lim ctl uuidParse S tdEnv)

def cliTryDecryptSpecPPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget.tryDecryptPlacedSpecP
      C A lim ctl uuidParse S tdEnv)

theorem cliTryDecryptSpecPlaced_onPanic_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st : M.σ) :
    (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st) =
      tryDecryptOnPanic C parse S x := rfl

theorem cliTryDecryptTightSpecPlaced_onPanic_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st : M.σ) :
    (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st) =
      tryDecryptOnPanicTight C S parse x := rfl

theorem cliTryDecryptSpecPPlaced_onPanic_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st : M.σ) :
    (cliTryDecryptSpecPPlaced C A lim ctl parse S tdEnv).onPanic (x, st) =
      tryDecryptOnPanic C parse S x := rfl

theorem reaches_outcome_weaken_tight_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s) :
    reaches_outcome P (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-! ## Budget-Threaded Segment Seams -/

def ErrTailTightSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    reaches_outcome prog (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

def S0PSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (cliTryDecryptSpecPPlaced C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A lim st_init ctl x R s0)

def S1TightSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
      reaches_outcome prog (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

/-- Pinned `S1` (`LoadRatchet`) CLI tight seam contract recording
`trGhostCaps trG = s1InitCaps x.G` for deterministic downstream `SeamBudget` threading. -/
def S1TightSeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
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
      reaches_outcome prog (cliTryDecryptTightSpecPlaced C A lim ctl parse S tdEnv)
        (x, st_init) R s0 s
    | (.ok tr, st1) =>
      FitsEnv M lim st (s1OkEnv x) →
      ∃ s', Steps prog s s' ∧
        ∃ evs trG, s1OkEnv x evs ∧ trGhostCaps trG = s1InitCaps x.G ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

theorem S1TightSeamPinnedPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {s1OkEnv : TryDecryptGhost → List AllocEvent → Prop}
    (h : S1TightSeamPinnedPlaced prog entry C A lim ctl parse S tdEnv s1OkEnv) :
    S1TightSeamPlaced prog entry C A lim ctl parse S tdEnv s1OkEnv := by
  intro x st_init st R s0 s hst hcode
  have h' := h x st_init st R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact id
  · rintro hfn hfit
    obtain ⟨s', hsteps, evs, trG, hevs, _, hfc⟩ := hfn hfit
    exact ⟨s', hsteps, evs, trG, hevs, hfc⟩

def S2SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    FindChainStatePlaced entry A lim st ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    match tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
    | .ok (some ck) =>
      reaches_pc prog (segConsumeMsgKeyPC_at entry) s
        (ConsumeMsgKeyStatePlaced entry A lim st ctl x trG tr st1 ck 0 R s0)
    | .ok none =>
      reaches_pc prog (segDhStepPC_at entry) s
        (DhStepStatePlaced entry A lim st ctl x trG tr st1 R s0)
    | .error e =>
      reaches_pc prog (errTailPC_at entry) s
        (ErrTailStatePlaced entry A lim st ctl x trG tr st1 e 0 R s0)

def S3TightSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R))

/-- Pinned `S3` (`DhStep`) CLI tight seam contract recording
`trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length`
on the `.ok ck` branch for deterministic downstream `SeamBudget` threading. -/
def S3TightSeamPinnedPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    ∃ s', Steps prog s s' ∧
      ((match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | (.ok ck, r1) =>
          ∃ evs trG', s3Env x trG tr evs ∧
            trGhostCaps trG' = s3AfterCaps (trGhostCaps trG) tr.ratchet.receiverChains.length ∧
            ConsumeMsgKeyStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 ck draws R s0 s'
        | (.error e, _) =>
          ∃ evs trG' r1, s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
       (s'.status = .Panicked ∧ s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R))

theorem S3TightSeamPinnedPlaced.toUnpinned [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (h : S3TightSeamPinnedPlaced prog entry C A lim ctl parse S s3Env) :
    S3TightSeamPlaced prog entry C A lim ctl parse S s3Env := by
  intro x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  obtain ⟨s', hsteps, hok | hpan⟩ :=
    h x st trG tr st1 R s0 s hfrom hfind hlen hsp hrest hfit hst hcode
  · refine ⟨s', hsteps, Or.inl ?_⟩
    revert hok
    rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with ⟨_ | ck, r1⟩
    · exact id
    · rintro ⟨evs, trG', hevs, _, hcmk⟩
      exact ⟨evs, trG', hevs, hcmk⟩
  · exact ⟨s', hsteps, Or.inr hpan⟩

def S4SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s4Env x trG tr ck) →
    ConsumeMsgKeyStatePlaced entry A lim st ctl x trG tr st1 ck draws R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
        x.msgType) tr.ratchet with
    | (.ok mkg, r2) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG', s4Env x trG tr ck evs ∧
            PqRecvStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r2 } st1 mkg draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps prog s s' ∧
        ((e ≠ .panic ∧ ∃ evs trG', s4Env x trG tr ck evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (e = .panic ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

def S5WTSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64) (F0 : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    x.st.pqRatchetState.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    FitsEnv M lim st (s5Env x tr) →
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A lim st ctl x trG tr st1 mkg draws (F0 ∗ R) s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            DeriveKeysStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 mkg newPqrState pqrKey draws (F0 ∗ R) s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 e draws (F0 ∗ R) s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

def S6SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (s6Env : MessageKeyGenerator → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator)
    (newPqrState : List (BitVec 8)) (pqrKey : Salt) (draws : Nat)
    (R : SepProp) (s0 s : State),
    mkg.seed.length = 32 →
    FitsEnv M lim st (s6Env mkg) →
    DeriveKeysStatePlaced entry A lim st ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s →
    reaches_pc prog (segVerifyMacPC_at entry) s
      (fun s' => ∃ evs, s6Env mkg evs ∧
        VerifyMacStatePlaced entry A lim (M.stepEvents evs st) ctl
          x trG tr st1 (mkg.generateKeys C.F pqrKey) newPqrState draws R s0 s')

def S7SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s7Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s7Env x tr mks newPqrState) →
    VerifyMacStatePlaced entry A lim st ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    if x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse parse) x.rem x.loc)
        tr.remoteIdentityKey tr.localIdentityKey mks.macKey then
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s7Env x tr mks newPqrState evs ∧
            AesDecryptStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 mks newPqrState draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s7Env x tr mks newPqrState evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

def S8SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s8Env x mks newPqrState) →
    AesDecryptStatePlaced entry A lim st ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    match aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
    | some pt =>
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s8Env x mks newPqrState evs ∧
            ApplyRatchetStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 newPqrState pt draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | none =>
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s8Env x mks newPqrState evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 (.invalidMessage x.msgType .badCiphertext) draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

def S9SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (R : SepProp) (s0 s : State),
    (x.model C S parse).1 = .ok pt →
    (x.model C S parse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st
      (s9Env x trG tr st1 newPqrState) →
    ApplyRatchetStatePlaced entry A lim st ctl x trG tr st1 newPqrState pt
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (cliTryDecryptSpecPlaced C A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

end LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
