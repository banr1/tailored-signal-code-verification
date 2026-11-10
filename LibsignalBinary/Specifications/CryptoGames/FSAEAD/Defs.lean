/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Forward-secure AEAD: syntax and security game (ACD19 Def. 14, Fig. 5, Def. 15)

**Trusted in part.** The theorems of `Computational/Theorems/` use only `Adversary`,
`AdversaryComp`, `FSAEADScheme`, `ReceiveResult`, `spec` from this file: read them. Everything else
here is checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Syntax (`FSAEADScheme`) and hidden-bit security game (`game`, `advantage`, `MakesAtMostQueries`) for
forward-secure AEAD after ACD19 §4.2.1 (Defs. 14–15, Fig. 5). Pure state transitions `transmit`,
`challenge`, `corruptSender`, `corruptReceiver`, `deliver`, and `inject` operate on `State`,
`Record`, and `isCompromised`.

Deviations in this file: DEV-FS1, DEV-FS2, DEV-FS3, DEV-FS4, DEV-FS5, DEV-FS6, DEV-FS11, DEV-FS21.
Companion FS-AEAD deviations appear in `Construction.lean` (DEV-FS7, DEV-FS10), `Security.lean`
(DEV-FS12, DEV-FS15), `SecurityWith.lean` (DEV-FS17), `PubDefs.lean` (DEV-FS19, DEV-FS20),
`Theorem5.lean` (DEV-FS16), and `Theorem5On.lean` (DEV-FS18); see `Computational/docs/DEVIATIONS.md`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

/-- Deterministic FS-AEAD scheme (ACD19 Def. 14).

**DEV-FS11 (formalization): no memory management.** `FS-Stop` and `FS-Max` (erasing old skipped keys
with no formal requirement) are omitted; the SM layer never erases sessions. -/
structure FSAEADScheme (Key SenderState ReceiverState AssocData Message Ciphertext : Type) where
  /-- `FS-Init-S`: initial sender state from the shared key. -/
  initSender : Key → SenderState
  /-- `FS-Init-R`: initial receiver state from the shared key. -/
  initReceiver : Key → ReceiverState
  /-- `FS-Send`: encrypt a message with associated data, returning the updated state and ciphertext. -/
  send : SenderState → AssocData → Message → SenderState × Ciphertext
  /-- `FS-Rcv`: decrypt a ciphertext with associated data, returning `(state', idx, msg)` or `none`. -/
  receive : ReceiverState → AssocData → Ciphertext → Option (ReceiverState × ℕ × Message)
  /-- Correctness skip window: `B` accepts honest ciphertexts up to `maxSkip` indices ahead of the
  highest accepted index (`0` = in-order; libsignal: `25,000`).

  **DEV-FS5 (libsignal): correctness only inside the skip window.** `deliver` requires acceptance
  only for records with `idx ≤ receiverIdx + maxSkip + 1`. Rejected records remain in transit so
  they cannot be re-submitted via `inject` as false forgeries or prematurely unlock `corruptReceiver`
  while a challenge is pending. -/
  maxSkip : ℕ

namespace FSAEAD

/-- Result of a receive oracle: `rejected`, or `accepted i m` (`m = none` when masked for a challenge). -/
inductive ReceiveResult (Message : Type) where
  | rejected
  | accepted (i : ℕ) (m : Option Message)
  deriving DecidableEq

/-- ACD19 Fig. 5 oracle interface (`transmit`, `challenge`, `corruptSender`, `corruptReceiver`,
`deliver`, `inject`).

**DEV-FS3 (formalization): `req` and `end`.** Failed `req` preconditions and calls after `ended`
return `none` without modifying state; `FS-Rcv` errors leave `v_B` unchanged. -/
abbrev spec (SenderState ReceiverState AssocData Message Ciphertext : Type) :=
  ((AssocData × Message) →ₒ Option Ciphertext)
  + ((AssocData × Message × Message) →ₒ Option Ciphertext)
  + (Unit →ₒ Option SenderState)
  + (Unit →ₒ Option (SenderState × ReceiverState))
  + ((AssocData × Ciphertext) →ₒ Option (ReceiveResult Message))
  + ((AssocData × Ciphertext) →ₒ Option (ReceiveResult Message))

/-- Computation with uniform coins and the Fig. 5 FS-AEAD oracles. -/
abbrev AdversaryComp (SenderState ReceiverState AssocData Message Ciphertext : Type) :=
  OracleComp (unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)

/-- FS-AEAD adversary outputting a Boolean guess for `b`. -/
abbrev Adversary (SenderState ReceiverState AssocData Message Ciphertext : Type) :=
  AdversaryComp SenderState ReceiverState AssocData Message Ciphertext Bool

variable {Key SenderState ReceiverState AssocData Message Ciphertext : Type}

section Queries

local notation "Comp" => AdversaryComp SenderState ReceiverState AssocData Message Ciphertext

def transmitQuery (a : AssocData) (m : Message) : Comp (Option Ciphertext) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inl (.inl (.inl (.inl (.inl (a, m)))))))

def challengeQuery (a : AssocData) (m₀ m₁ : Message) : Comp (Option Ciphertext) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁)))))))

def corruptSenderQuery : Comp (Option SenderState) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inl (.inl (.inl (.inr ())))))

def corruptReceiverQuery : Comp (Option (SenderState × ReceiverState)) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inl (.inl (.inr ()))))

def deliverQuery (a : AssocData) (e : Ciphertext) : Comp (Option (ReceiveResult Message)) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inl (.inr (a, e))))

def injectQuery (a : AssocData) (e : Ciphertext) : Comp (Option (ReceiveResult Message)) :=
  query (spec := unifSpec + spec SenderState ReceiverState AssocData Message Ciphertext)
    (.inr (.inr (a, e)))

end Queries

/-- In-transit record `(i, a, m, e)` sent by `A` and not yet accepted by `B` (ACD19 Fig. 5 `trans`). -/
structure Record (AssocData Message Ciphertext : Type) where
  idx : ℕ
  ad : AssocData
  msg : Message
  ct : Ciphertext

/-- ACD19 Fig. 5 game state. -/
structure State (SenderState ReceiverState AssocData Message Ciphertext : Type) where
  senderState : SenderState
  receiverState : ReceiverState
  b : Bool
  lastSentIdx : ℕ := 0
  /-- `lastSentIdx` at the first `corruptSender` query, or `none` if uncorrupted (DEV-FS1). -/
  senderCorruptedAt : Option ℕ := none
  /-- Highest index accepted by `B` so far (`0` initially), bounding the skip window (DEV-FS5). -/
  receiverIdx : ℕ := 0
  ended : Bool := false
  win : Bool := false
  inTransit : List (Record AssocData Message Ciphertext) := []
  challengesInTransit : List ℕ := []

namespace State

/-- Whether index `i` was sent after the first `corruptSender` query.

**DEV-FS1 (paper fix): every index after the first `corr-A` is compromised.** In ACD19 Fig. 5,
`comp` records only messages sent via `transmit-A` after `corr-A`, making post-`corr-A` forgeries at
`iA + 1` trivial wins; marking all `i > senderCorruptedAt` compromised excludes these trivial wins. -/
def isCompromised (st : State SenderState ReceiverState AssocData Message Ciphertext) (i : ℕ) :
    Bool :=
  match st.senderCorruptedAt with
  | some j => decide (j < i)
  | none => false

/-- Remove index `i` from `inTransit` and `challengesInTransit` (ACD19 Fig. 5 `delete(i)`). -/
def removeFromTransit (st : State SenderState ReceiverState AssocData Message Ciphertext)
    (i : ℕ) : State SenderState ReceiverState AssocData Message Ciphertext :=
  { st with inTransit := st.inTransit.filter (·.idx != i),
            challengesInTransit := st.challengesInTransit.filter (· != i) }

end State

section Oracles

variable (fs : FSAEADScheme Key SenderState ReceiverState AssocData Message Ciphertext)
  (st : State SenderState ReceiverState AssocData Message Ciphertext)

/-- ACD19 Fig. 5 `transmit-A(a, m)`: encrypt `m` at the next index and record it in transit. -/
def transmit (a : AssocData) (m : Message) :
    Option Ciphertext × State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended then (none, st) else
  let i := st.lastSentIdx + 1
  let (senderState', e) := fs.send st.senderState a m
  (some e, { st with senderState := senderState', lastSentIdx := i,
                     inTransit := ⟨i, a, m, e⟩ :: st.inTransit })

/-- ACD19 Fig. 5 `chall-A(a, m₀, m₁)`: encrypt `m_b` at the next index if uncorrupted.

**DEV-FS4 (formalization): `|m₀| = |m₁|` is not checked.** Length equality is captured by the type
`Message` (constant-length per session in libsignal, DEV-AEAD2). -/
def challenge (a : AssocData) (m₀ m₁ : Message) :
    Option Ciphertext × State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended || st.senderCorruptedAt.isSome then (none, st) else
  let i := st.lastSentIdx + 1
  let m := if st.b then m₁ else m₀
  let (senderState', e) := fs.send st.senderState a m
  (some e, { st with senderState := senderState', lastSentIdx := i,
                     inTransit := ⟨i, a, m, e⟩ :: st.inTransit,
                     challengesInTransit := i :: st.challengesInTransit })

/-- ACD19 Fig. 5 `corr-A`: reveal `A`'s current state and mark subsequent indices compromised. -/
def corruptSender :
    Option SenderState × State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended then (none, st) else
  (some st.senderState,
    { st with senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx) })

/-- ACD19 Fig. 5 `corr-B`: reveal both states and end the game when no uncompromised record is in
transit.

**DEV-FS6 (paper fix): `corr-B` also waits for uncompromised records.** ACD19 Fig. 5 blocks `corr-B`
only while a challenge is in transit, which breaks the Thm 5 PRG hybrid hop at `iB` when
non-challenge honest records remain pending; blocking on any uncompromised in-transit record fixes
this. -/
def corruptReceiver :
    Option (SenderState × ReceiverState) ×
      State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended || !st.challengesInTransit.isEmpty ||
      st.inTransit.any (fun r => !st.isCompromised r.idx) then (none, st) else
  (some (st.senderState, st.receiverState), { st with ended := true })

/-- ACD19 Fig. 5 `deliver-B(a, e)`: deliver an in-transit record to `B`, masking the output message
for challenges and checking correctness on uncompromised in-window records.

**DEV-FS2 (paper fix): no correctness win on compromised records.** Correctness is required only
when `!st.isCompromised r.idx`, since adversarial injections at compromised indices can cause `B` to
reject the corresponding honest record.

**DEV-FS21 (formalization): which record is delivered.** Selects the most recent matching record via
`List.find?` (unique for Fig. 6 indexed ciphertexts). -/
def deliver [DecidableEq AssocData] [DecidableEq Message] [DecidableEq Ciphertext]
    (a : AssocData) (e : Ciphertext) :
    Option (ReceiveResult Message) × State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended then (none, st) else
  match st.inTransit.find? (fun r => r.ad == a && r.ct == e) with
  | none => (none, st)
  | some r =>
    let inWindow := decide (r.idx ≤ st.receiverIdx + fs.maxSkip + 1)
    let mustBeCorrect := !st.isCompromised r.idx && inWindow
    match fs.receive st.receiverState a e with
    | none =>
      (some .rejected, { st with win := st.win || mustBeCorrect })
    | some (receiverState', i', m') =>
      let incorrect := mustBeCorrect && (i' != r.idx || m' != r.msg)
      let out := if st.challengesInTransit.contains r.idx then none else some m'
      let st' := { st with receiverState := receiverState', receiverIdx := max st.receiverIdx i',
                           win := st.win || incorrect }
      (some (.accepted i' out), st'.removeFromTransit r.idx)

/-- ACD19 Fig. 5 `inject-B(a, e)`: submit a non-in-transit ciphertext `(a, e)` to `B`, setting
`win` if accepted at an uncompromised index. -/
def inject [DecidableEq AssocData] [DecidableEq Ciphertext] (a : AssocData) (e : Ciphertext) :
    Option (ReceiveResult Message) × State SenderState ReceiverState AssocData Message Ciphertext :=
  if st.ended || st.inTransit.any (fun r => r.ad == a && r.ct == e) then (none, st) else
  match fs.receive st.receiverState a e with
  | none => (some .rejected, st)
  | some (receiverState', i', m') =>
    let forged := !st.isCompromised i'
    let st' := { st with receiverState := receiverState', receiverIdx := max st.receiverIdx i',
                         win := st.win || forged }
    (some (.accepted i' (some m')), st'.removeFromTransit i')

end Oracles

section Game

variable [DecidableEq AssocData] [DecidableEq Message] [DecidableEq Ciphertext]
  (fs : FSAEADScheme Key SenderState ReceiverState AssocData Message Ciphertext)

local notation "GameM" =>
  StateT (State SenderState ReceiverState AssocData Message Ciphertext) ProbComp

def transmitImpl : QueryImpl ((AssocData × Message) →ₒ Option Ciphertext) GameM :=
  fun q => modifyGet (transmit fs · q.1 q.2)

def challengeImpl : QueryImpl ((AssocData × Message × Message) →ₒ Option Ciphertext) GameM :=
  fun q => modifyGet (challenge fs · q.1 q.2.1 q.2.2)

def corruptSenderImpl : QueryImpl (Unit →ₒ Option SenderState) GameM :=
  fun _ => modifyGet corruptSender

def corruptReceiverImpl : QueryImpl (Unit →ₒ Option (SenderState × ReceiverState)) GameM :=
  fun _ => modifyGet corruptReceiver

def deliverImpl :
    QueryImpl ((AssocData × Ciphertext) →ₒ Option (ReceiveResult Message)) GameM :=
  fun q => modifyGet (deliver fs · q.1 q.2)

def injectImpl :
    QueryImpl ((AssocData × Ciphertext) →ₒ Option (ReceiveResult Message)) GameM :=
  fun q => modifyGet (inject fs · q.1 q.2)

/-- Combined `QueryImpl` for all ACD19 Fig. 5 oracles. -/
def oracleImpl : QueryImpl (spec SenderState ReceiverState AssocData Message Ciphertext) GameM :=
  transmitImpl fs + challengeImpl fs + (corruptSenderImpl : QueryImpl _ GameM)
    + (corruptReceiverImpl : QueryImpl _ GameM) + deliverImpl fs + injectImpl fs

/-- Initial game state for shared key `k` and challenge bit `b`. -/
def initState (k : Key) (b : Bool) :
    State SenderState ReceiverState AssocData Message Ciphertext :=
  { senderState := fs.initSender k, receiverState := fs.initReceiver k, b }

/-- ACD19 Fig. 5 FS-AEAD hidden-bit game. -/
def game [SampleableType Key]
    (A : Adversary SenderState ReceiverState AssocData Message Ciphertext) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget GameM + oracleImpl fs
  let (b', st) ← (simulateQ impl A).run (initState fs k b)
  return b == b' || st.win

/-- FS-AEAD advantage `Adv^{fs-aead}(A) = 2 · |Pr[A wins] - 1/2|` (ACD19 Def. 15, DEV-CKA7). -/
noncomputable def advantage [SampleableType Key]
    (A : Adversary SenderState ReceiverState AssocData Message Ciphertext) : ℝ≥0∞ :=
  𝒟[game fs A].boolBias

/-- `A` makes at most `q` queries to the Fig. 5 FS-AEAD oracles. -/
def MakesAtMostQueries (A : Adversary SenderState ReceiverState AssocData Message Ciphertext)
    (q : ℕ) : Prop :=
  A.IsQueryBoundP (· matches .inr _) q

end Game

section RestrictedAD

variable {SS RS AD Msg C : Type}

end RestrictedAD

end FSAEAD

namespace AEADScheme

variable {K AD M C : Type}

end AEADScheme

end CryptoGames
