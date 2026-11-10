/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Budget-Threaded Checkpoint States, Specs & Segment Seams for `try_decrypt_with_state`

Defines `RustCliAllocBudget M` / `SeamBudget` checkpoint states (`ErrTailStatePlaced` ..
`ApplyRatchetStatePlaced` threading `A.atState lim st s`), whole-function contracts
(`tryDecryptRawSpecPlaced`, `tryDecryptSpecPlaced`, and `decFn` variants with `onOom = ⌜False⌝` and
`allocFailedIn` dropped from `onPanic`), and segment seams (`S0SeamPlaced` .. `S9SeamPlaced`,
`ErrTailSeamPlaced`, and `X` variants).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto ChainKey MessageKeyGenerator MessageKeys Mut RatchetState
  SessionState SignalProtocolError TripleRatchet aesCbcDecrypt
)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf decryptDraws serviceIdParse serializeAddresses
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel SeedsLen32 TrGhost TryDecryptGhost rootStack withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  segLoadRatchetPC_at segConsumeMsgKeyPC_at segDhStepPC_at
  segVerifyMacPC_at errTailPC_at
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv FreeOnlyEvs
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)

/-! ## 1. Budget-Threaded Checkpoint States -/

def ErrTailStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

def ErrTailStateXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (e : SignalProtocolError) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ErrTailStateXPlaced
    entry (A.atState lim st s) ctl x trG tr st1 e draws R s0 s

theorem ErrTailStatePlaced.toX [LibsignalPlacement] {M : AllocCostModel}
    {entry : BitVec 64} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ctl : BitVec 64} {x : TryDecryptGhost} {trG : TrGhost}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {e : SignalProtocolError} {draws : Nat} {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced entry A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateXPlaced entry A lim st ctl x trG tr st1 e draws R s0 s :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ErrTailStatePlaced.toX h

def LoadRatchetStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.LoadRatchetStatePlaced
    entry (A.atState lim st s) ctl x R s0 s

def FindChainStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.FindChainStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 R s0 s

def DhStepStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStepStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 R s0 s

def ConsumeMsgKeyStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (ck : ChainKey) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ConsumeMsgKeyStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 ck draws R s0 s

def PqRecvStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.PqRecvStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mkg draws R s0 s

def DeriveKeysStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (newPqrState : List (BitVec 8)) (pqrKey : Salt)
    (draws : Nat) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.DeriveKeysStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mkg newPqrState pqrKey draws R s0 s

def VerifyMacStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.VerifyMacStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mks newPqrState draws R s0 s

def AesDecryptStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mks : MessageKeys) (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AesDecryptStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 mks newPqrState draws R s0 s

def ApplyRatchetStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (entry : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.ApplyRatchetStatePlaced
    entry (A.atState lim st s) ctl x trG tr st1 newPqrState pt draws R s0 s

/-! ## 2. Budget-Threaded Whole-Function `try_decrypt_with_state` Contracts -/

/-- Panic postcondition of budget-threaded `try_decrypt_with_state` (`allocFailedIn` dropped;
    retains only legitimate model / SPQR panics). Independent of `tdEnv` and `st_init`. -/
def tryDecryptOnPanic (C : Crypto) (uuidParse : UuidParser) (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜((x.model C S uuidParse).1 = .error .panic ∨
      S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
    s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Panic postcondition of budget-threaded `tryDecryptFnSpecPlaced` (`decFn` variant). -/
def tryDecryptFnOnPanic (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (uuidParse : UuidParser) (S : SpqrModel)
    (x : TryDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜((x.modelFn C decFn S uuidParse).1 = .error .panic ∨
      S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
    s0.trace <+: sf.trace⌝ ∗ anyHeap

def tryDecryptRawSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptRawSpecPlaced
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf => tryDecryptOnPanic C uuidParse S x s0 sf

def tryDecryptSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (tryDecryptRawSpecPlaced C A lim ctl uuidParse S tdEnv)

def tryDecryptFnRawSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := (tryDecryptRawSpecPlaced C A lim ctl uuidParse S tdEnv).pre
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptFnRawSpecPlaced
        C decFn (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf => tryDecryptFnOnPanic C decFn uuidParse S x s0 sf

def tryDecryptFnSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl (tryDecryptFnRawSpecPlaced C decFn A lim ctl uuidParse S tdEnv)

/-! ## 3. Budget-Threaded Segment Seams (`S0SeamPlaced` .. `S9SeamPlaced`, `ErrTailSeamPlaced`) -/

def ErrTailSeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s

def S0SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A lim st_init ctl x R s0)

def S1SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

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

def S3SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
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
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))

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

def S5SeamPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s5Env x tr) →
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A lim st ctl x trG tr st1 mkg draws R s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            DeriveKeysStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanic C parse S x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 e draws R s0 s' ∧
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
    reaches_outcome prog (tryDecryptSpecPlaced C A lim ctl parse S tdEnv) (x, st_init) R s0 s

/-! ## 4. `Stage2ContractsX` (`X`) Budget-Threaded Segment Seams -/

def ErrTailSeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

def S0SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    s0.pc = entry → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) →
    reaches_pc prog (segLoadRatchetPC_at entry) s0
      (LoadRatchetStatePlaced entry A lim st_init ctl x R s0)

def S1SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
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
        ∃ evs trG, s1OkEnv x evs ∧
          FindChainStatePlaced entry A lim (M.stepEvents evs st) ctl x trG tr st1 R s0 s'

abbrev S2SeamXPlaced [LibsignalPlacement] := @S2SeamPlaced

def S3SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
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
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs trG' r1', s3Env x trG tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r1' } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

def S4SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
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
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    | (.error e, r2) =>
      ∃ s', Steps prog s s' ∧
        ((e ≠ .panic ∧ ∃ evs trG', s4Env x trG tr ck evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG' { tr with ratchet := r2 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (e = .panic ∧ s0.trace <+: s'.trace) ∧
           (s'.mem ⊨ anyHeap ∗ R)))

def S5SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s5Env x tr) →
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A lim st ctl x trG tr st1 mkg draws R s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            DeriveKeysStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 mkg newPqrState pqrKey draws R s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((∃ evs, s5Env x tr evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 e draws R s0 s' ∧
            S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

abbrev S6SeamXPlaced [LibsignalPlacement] := @S6SeamPlaced

def S7SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
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
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    else
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s7Env x tr mks newPqrState evs ∧
            ErrTailStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 (.invalidMessage x.msgType .macFailed) draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

def S8SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (s8Env : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st : M.σ) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mks : MessageKeys)
    (newPqrState : List (BitVec 8)) (draws : Nat)
    (R : SepProp) (s0 s : State),
    FitsEnv M lim st (s8Env x mks newPqrState) →
    AesDecryptStatePlaced entry A lim st ctl x trG tr st1 mks newPqrState draws R s0 s →
    prog.CodeLoaded s.mem →
    match decFn x.msg.ciphertext (keyToBytes32 mks.cipherKey) (blockToBytesLE mks.iv) with
    | some pt =>
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s8Env x mks newPqrState evs ∧
            ApplyRatchetStatePlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 newPqrState pt draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))
    | none =>
      ∃ s' : State, Steps prog s s' ∧
        ((∃ evs, s8Env x mks newPqrState evs ∧
            ErrTailStateXPlaced entry A lim (M.stepEvents evs st) ctl
              x trG tr st1 (.invalidMessage x.msgType .badCiphertext) draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptFnOnPanic C decFn parse S x s0 s' ∗ R)))

def S9SeamXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (prog : Program) (entry : BitVec 64)
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (s9Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop) : Prop :=
  ∀ (x : TryDecryptGhost) (st_init st : M.σ) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (newPqrState pt : List (BitVec 8)) (R : SepProp) (s0 s : State),
    (x.modelFn C decFn S parse).1 = .ok pt →
    (x.modelFn C decFn S parse).2 =
      (({ tr with pqrState := newPqrState }).applyToSessionState st1).clearUnacknowledgedPreKeyMessage →
    SeamBudget M lim (tdEnv (tryDecryptEnvArgs x)) st_init st
      (s9Env x trG tr st1 newPqrState) →
    ApplyRatchetStatePlaced entry A lim st ctl x trG tr st1 newPqrState pt
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv)
      (x, st_init) R s0 s

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
