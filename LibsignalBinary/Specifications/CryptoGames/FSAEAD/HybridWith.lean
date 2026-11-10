/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid

/-!
# Hybrid games and reductions of ACD19 Thm 5, with an AD-dependent ideal ciphertext

**Trusted in part.** The CLI security theorems (`Theorems/Main.lean` under `Computational/`,
`Oom/Supporting.lean` under `Computational/Proofs/LibsignalCli/`) use only `IndexedOtccaSpec` and
`slotToHybridHopIndex` from this file: read them. The rest is used by no theorem of
`Computational/Theorems/`. The Thm 5 hybrids and reductions among it are part of the statement of
`theorem5`: read them to trust it. Every proof is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Hybrid encrypting oracle (`encIdxWith`, `otOpsWith`), `(ℕ × AD)`-indexed OT-CCA interface
(`IndexedOtccaSpec`, `IndexedOtccaState`, `otImpl`), multi-slot OT-CCA reduction
(`multiSlotOtccaReduction`), and hop-index encoding (`slotToHybridHopIndex`) with AD-dependent ideal
ciphertexts `ideal (i, a)` (DEV-FS17).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type}

section Oracles

variable {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
  [SampleableType MK] [SampleableType CK]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (P : Params) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))

local notation "St" => HSt CK MK AD M C

/-- Encrypt `msg` with header `(i, a)` under index `i`: an ideal index gets a ciphertext drawn from
`ideal (i, a)`; the special index uses the OT-CCA oracle; a real index uses its message key. -/
def encIdxWith (i : ℕ) (a : AD) (msg : M) : StateT St m C := do
  let st ← getH
  match kind P ops st i, ops with
  | .ideal, _ => sampleH (ideal (i, a))
  | .special, some o => liftM (o.enc (i, a) msg)
  | _, _ =>
    match st.keys[i - 1]? with
    | some K => pure (ae.enc K (i, a) msg)
    | none => sampleH (ideal (i, a))

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

end Oracles

/-! ### Hybrid games and the reductions -/

section Games

variable [SampleableType MK] [SampleableType CK] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- The OT-CCA oracles as special operations (the placeholder answer to a second
`encrypt`, which cannot happen in the hybrid, is drawn from `ideal h`). -/
def otOpsWith :
    SpecialOps AD M C (OracleComp (unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C)) where
  enc h msg := do
    let r ← (query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (.inr (.inl (h, msg))))
    match r with
    | some e => pure e
    | none => liftM (ideal h)
  dec h e := query (spec := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C) (.inr (.inr (h, e)))

end Games

section Uniform

variable [SampleableType MK] [SampleableType CK] [SampleableType C]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

end Uniform

/-- `(ℕ × AD)`-indexed OT-CCA oracle interface (uniform coins plus `encrypt`/`decrypt`). -/
abbrev IndexedOtccaSpec (AD M C : Type) := unifSpec + AEADScheme.otccaSpec (ℕ × AD) M C

/-- `(ℕ × AD)`-indexed OT-CCA game state. -/
abbrev IndexedOtccaState (MK AD C : Type) := AEADScheme.OTCCAState MK (ℕ × AD) C

/-- `(ℕ × AD)`-indexed OT-CCA oracle implementation with AD-dependent ideal ciphertexts `ideal`. -/
def otImpl [DecidableEq AD] [DecidableEq C] (ideal : ℕ × AD → ProbComp C)
    (ae : AEADScheme MK (ℕ × AD) M C) :
    QueryImpl (IndexedOtccaSpec AD M C) (StateT (IndexedOtccaState MK AD C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (IndexedOtccaState MK AD C) ProbComp)
    + (ae.otccaEncryptAdIdeal ideal + ae.otccaDecrypt)

section MultiSlot

set_option linter.unusedSectionVars false

variable [SampleableType MK] [SampleableType CK] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : (ℕ × AD) → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C)
  (G : ℕ → PRGScheme CK (CK × MK))
  (maxSkip : ℕ)

/-- Multi-slot key kind: uncompromised message indices `i ≤ t` are `.ideal`, uncompromised
indices `t < i ≤ m` (when `ops.isSome`) are `.special`, and all other indices are `.real`. -/
def multiKind {m : Type → Type} (t mSlot : ℕ) (ops : Option (SpecialOps AD M C m))
    (st : HState CK MK AD M C) (i : ℕ) : Kind :=
  if i ≤ t && !st.isCompromised i then .ideal
  else if ops.isSome && i ≤ mSlot && !st.isCompromised i then .special
  else .real

/-- Multi-slot decryption at index `i`: `decIdx` with the index kinds of `multiKind` (ideal indices
reject, special ones use the OT-CCA `decrypt` oracle, real ones the message key). -/
def multiDecIdx {m : Type → Type} [Monad m]
    (t mSlot : ℕ) (ops : Option (SpecialOps AD M C m))
    (hint : Option M) (i : ℕ) (a : AD) (e : C) : StateT (HSt CK MK AD M C) m (Option M) := do
  match hint with
  | some msg => pure (some msg)
  | none =>
    let st ← getH
    match multiKind t mSlot ops st i, ops with
    | .ideal, _ => pure none
    | .special, some o => liftM (o.dec (i, a) e)
    | _, _ => pure ((st.keys[i - 1]?).bind fun K => ae.dec K (i, a) e)

/-- Multi-slot encryption at index `i`: `encIdxWith` with the index kinds of `multiKind` (ideal
indices get a ciphertext from `ideal (i, a)`, special ones use the OT-CCA `encrypt` oracle, real
ones the message key). -/
def multiEncIdxWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (t mSlot : ℕ) (ops : Option (SpecialOps AD M C m))
    (i : ℕ) (a : AD) (msg : M) : StateT (HSt CK MK AD M C) m C := do
  let st ← getH
  match multiKind t mSlot ops st i, ops with
  | .ideal, _ => sampleH (ideal (i, a))
  | .special, some o => liftM (o.enc (i, a) msg)
  | _, _ =>
    match st.keys[i - 1]? with
    | some K => pure (ae.enc K (i, a) msg)
    | none => sampleH (ideal (i, a))

/-- `B` receives `(i, e)` with associated data `a` using `multiDecIdx`. -/
def multiReceiveH {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (hint : Option M) (a : AD) (c : ℕ × C) : StateT (HSt CK MK AD M C) m (Option (ℕ × M)) := do
  let (i, e) := c
  let st ← getH
  if st.skipped.contains i then
    match ← multiDecIdx ae (P.t.getD 0) mSlot ops hint i a e with
    | some msg =>
      modifyH fun st => { st with skipped := st.skipped.filter (· != i) }
      pure (some (i, msg))
    | none => pure none
  else if i ≤ st.receiverIdx ∨ maxSkip < i - st.receiverIdx - 1 then pure none
  else if !P.la && st.lastSentIdx < i && !st.isCompromised i then pure none
  else do
    genUpTo G P D i
    match ← multiDecIdx ae (P.t.getD 0) mSlot ops hint i a e with
    | some msg =>
      modifyH fun st' => { st' with skipped := newSkipped st.receiverIdx i ++ st'.skipped }
      pure (some (i, msg))
    | none => pure none

/-- `deliver-B` using `multiReceiveH`. -/
def multiDeliverH {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (q : AD × (ℕ × C)) : StateT (HSt CK MK AD M C) m (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended then pure none else
  match st.inTransit.find? (fun r => r.ad == q.1 && r.ct == q.2) with
  | none => pure none
  | some r =>
    let inWindow := decide (r.idx ≤ st.receiverIdx + maxSkip + 1)
    let mustBeCorrect := !st.isCompromised r.idx && inWindow
    match ← multiReceiveH ae G maxSkip P mSlot D ops (some r.msg) q.1 q.2 with
    | none =>
      modifyH fun st' => { st' with win := st'.win || mustBeCorrect }
      pure (some .rejected)
    | some (i', m') =>
      let incorrect := mustBeCorrect && (i' != r.idx || m' != r.msg)
      let out := if st.challengesInTransit.contains r.idx then none else some m'
      modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                     win := st'.win || incorrect }).removeFromTransit r.idx
      pure (some (.accepted i' out))

/-- `inject-B` using `multiReceiveH`. -/
def multiInjectH {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (q : AD × (ℕ × C)) : StateT (HSt CK MK AD M C) m (Option (ReceiveResult M)) := do
  let st ← getH
  if st.ended || st.inTransit.any (fun r => r.ad == q.1 && r.ct == q.2) then pure none else
  match ← multiReceiveH ae G maxSkip P mSlot D ops none q.1 q.2 with
  | none => pure (some .rejected)
  | some (i', m') =>
    let forged := !st.isCompromised i'
    let lfNow := forged && decide (st.lastSentIdx < i')
    modifyH fun st' => ({ st' with receiverIdx := max st'.receiverIdx i',
                                   win := st'.win || forged, lf := st'.lf || lfNow,
                                   ended := st'.ended || (P.la && lfNow) }).removeFromTransit i'
    pure (some (.accepted i' (some m')))

/-- `transmit-A` of the multi-slot hybrid game. -/
def multiTransmitHWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (q : AD × M) : StateT (HSt CK MK AD M C) m (Option (ℕ × C)) := do
  let st ← getH
  if st.ended then pure none else do
  let i := st.lastSentIdx + 1
  genUpTo G P D i
  let e ← multiEncIdxWith ideal ae (P.t.getD 0) mSlot ops i q.1 q.2
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, q.2, (i, e)⟩ :: st.inTransit }
  pure (some (i, e))

/-- `chall-A` of the multi-slot hybrid game. -/
def multiChallengeHWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))
    (q : AD × M × M) : StateT (HSt CK MK AD M C) m (Option (ℕ × C)) := do
  let st ← getH
  if st.ended || st.senderCorruptedAt.isSome then pure none else do
  let i := st.lastSentIdx + 1
  let msg := if st.b then q.2.2 else q.2.1
  genUpTo G P D i
  let e ← multiEncIdxWith ideal ae (P.t.getD 0) mSlot ops i q.1 msg
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, msg, (i, e)⟩ :: st.inTransit,
              challengesInTransit := i :: st.challengesInTransit }
  pure (some (i, e))

/-- All Fig. 5 oracles of the multi-slot hybrid game. -/
def multiOraclesWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m)) :
    QueryImpl (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      (StateT (HSt CK MK AD M C) m) :=
  (multiTransmitHWith ideal ae G P mSlot D ops : QueryImpl _ _)
    + (multiChallengeHWith ideal ae G P mSlot D ops : QueryImpl _ _)
    + (corruptSenderH (m := m) (AD := AD) (M := M) (C := C) G P :
        QueryImpl (Unit →ₒ Option (RatchetSenderState CK)) (StateT (HSt CK MK AD M C) m))
    + (corruptReceiverH (m := m) (AD := AD) (M := M) (C := C) (MK := MK) G P :
        QueryImpl (Unit →ₒ Option (RatchetSenderState CK × RatchetReceiverState CK MK))
          (StateT (HSt CK MK AD M C) m))
    + (multiDeliverH ae G maxSkip P mSlot D ops : QueryImpl _ _)
    + (multiInjectH ae G maxSkip P mSlot D ops : QueryImpl _ _)

/-- The adversary's oracles in a multi-slot hybrid game. -/
def multiImplWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m)) :
    QueryImpl (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
      (ℕ × C)) (StateT (HSt CK MK AD M C) m) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (HSt CK MK AD M C) m)
    + multiOraclesWith ideal ae G maxSkip P mSlot D ops

/-- A multi-slot hybrid game in an ambient monad, from a given initial slot. -/
def multiRunWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (P : Params) (mSlot : ℕ) (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C m))
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) : m Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : m Bool)
  let z ← (simulateQ (multiImplWith ideal ae G maxSkip P mSlot D ops) A).run (hInit b sl)
  pure (hOut P.la z)

/-- **The multi-slot OT-CCA reduction for `N` chain positions.** Runs the hybrid game after all `N`
chain-PRG steps have been idealized (`hp N 0 la`), routing all uncompromised message indices
`1 ≤ i ≤ N` through the external `(ℕ × AD)`-indexed OT-CCA oracles `otOpsWith ideal`. -/
def multiSlotOtccaReduction (N : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C) :
    AEADScheme.OTCCAAdversary (ℕ × AD) M C :=
  multiRunWith ideal ae G maxSkip (hp N 0 la) N (DG G) (some (otOpsWith ideal)) A .unknown

end MultiSlot

/-- Sample a list of `n` independent uniform message keys. -/
def sampleKeys [SampleableType MK] : ℕ → ProbComp (List MK)
  | 0 => pure []
  | n + 1 => do
    let K ← $ᵗ MK
    let ks ← sampleKeys n
    pure (K :: ks)

/-- Initial multi-slot `OTCCA` state for `N` slots from a pre-sampled key list `ks` of length `N`
(using `K₀` outside `1 ≤ i ≤ ks.length`). -/
def initOStM (b : Bool) (K₀ : MK) (ks : List MK) (i : ℕ) : IndexedOtccaState MK AD C :=
  ⟨if i = 0 then K₀ else ks[i - 1]?.getD K₀, b, none⟩

/-- Single-slot reduction implementation at step `k` (`0 ≤ k < N`): forwards queries at slot
`k + 1` to the external `IndexedOtccaSpec AD M C` oracle, runs `implR` on slots `1 ≤ i ≤ k`, and runs `implL`
on all remaining slots. -/
def slotRedImpl {SL SR : Type}
    (implL : QueryImpl (IndexedOtccaSpec AD M C) (StateT SL ProbComp))
    (implR : QueryImpl (IndexedOtccaSpec AD M C) (StateT SR ProbComp))
    (k : ℕ) : QueryImpl (IndexedOtccaSpec AD M C)
      (StateT ((ℕ → SL) × (ℕ → SR)) (OracleComp (IndexedOtccaSpec AD M C)))
  | .inl n => StateT.lift (liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inl n)))
  | .inr (.inl ⟨h, m⟩) =>
    if h.1 = k + 1 then
      StateT.lift (liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inr (.inl ⟨h, m⟩))))
    else if 1 ≤ h.1 ∧ h.1 ≤ k then
      StateT.mk fun s => liftM ((fun r => (r.1, (s.1, Function.update s.2 h.1 r.2))) <$>
        (implR (.inr (.inl ⟨h, m⟩))).run (s.2 h.1))
    else
      StateT.mk fun s => liftM ((fun r => (r.1, (Function.update s.1 h.1 r.2, s.2))) <$>
        (implL (.inr (.inl ⟨h, m⟩))).run (s.1 h.1))
  | .inr (.inr ⟨h, e⟩) =>
    if h.1 = k + 1 then
      StateT.lift (liftM (OracleSpec.query (spec := IndexedOtccaSpec AD M C) (.inr (.inr ⟨h, e⟩))))
    else if 1 ≤ h.1 ∧ h.1 ≤ k then
      StateT.mk fun s => liftM ((fun r => (r.1, (s.1, Function.update s.2 h.1 r.2))) <$>
        (implR (.inr (.inr ⟨h, e⟩))).run (s.2 h.1))
    else
      StateT.mk fun s => liftM ((fun r => (r.1, (Function.update s.1 h.1 r.2, s.2))) <$>
        (implL (.inr (.inr ⟨h, e⟩))).run (s.1 h.1))

/-- Map slot `j < 2 * q + (maxSkip + 1)` to its encoded hybrid hop index `m`, which the single-slot
reductions decode into chain position `m / 2` and lookahead bit `isLookaheadHop m = (m % 2 == 1)`:
- for `j < 2 * q`, `slotToHybridHopIndex q j = j` (interleaving `2 * k` and `2 * k + 1` for `k < q`);
- for `j = 2 * q + d`, `slotToHybridHopIndex q j = 2 * (q + d) + 1` (the remaining lookahead hops `k ≥ q`). -/
def slotToHybridHopIndex (q j : ℕ) : ℕ :=
  if j < 2 * q then j else 2 * (j - q) + 1

end CryptoGames.FSAEAD.Thm5

