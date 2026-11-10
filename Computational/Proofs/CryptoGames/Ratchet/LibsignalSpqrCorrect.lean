/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.LibsignalSpqr
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# SPQR acceptance window and honest-correctness game

**Checked by Lean.**

Ghost-logged SPQR wrapper (`Spqr.withLog`), symmetric-chain acceptance window (`spqrWindowOk`,
DEV-SPQR7), and honest-traffic correctness game (`Corr.spqrGame`, `Corr.SpqrHonestCorrect`)
replacing the idealized `SpqrOffCorrect` hypothesis (DEV-LS24).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace LibsignalSession

open HKDF

/-! ## Ghost log -/

/-- Ghost log of committed SPQR `pq_ratchet` payloads, newest first. -/
structure SpqrLog where
  sent : List (List (BitVec 8))
  recvd : List (List (BitVec 8))
  deriving DecidableEq

instance : Inhabited SpqrLog := ⟨⟨[], []⟩⟩

variable {PQ PQC : Type}

/-- Augments `S` with a ghost `SpqrLog` recording successful `send` and `recv` payloads. -/
def Spqr.withLog (S : Spqr PQ PQC) : Spqr (PQ × SpqrLog) PQC where
  init dir k := (S.init dir k, default)
  send st r := (S.send st.1 r).map fun x => ((x.1, { st.2 with sent := x.2.2 :: st.2.sent }), x.2.1, x.2.2)
  recv st msg := (S.recv st.1 msg).map fun x => ((x.1, { st.2 with recvd := msg :: st.2.recvd }), x.2)
  sendPanics st r := S.sendPanics st.1 r
  recvPanics st msg := S.recvPanics st.1 msg

def Params.withSpqrLog (P : Params PQ PQC) : Params (PQ × SpqrLog) PQC :=
  { P with spqr := P.spqr.withLog }

/-! ## Acceptance window -/

/-- Extracts `(epoch, index)` from an SPQR message preamble. -/
def spqrPos (msg : List (BitVec 8)) : Option (ℕ × ℕ) :=
  (CryptoVerification.LibsignalSpqr.msgPreamble? msg).map fun p => (p.epoch.toNat, p.index.toNat)

/-- Largest header epoch among committed sends (`0` if none). -/
def SpqrLog.maxSendEpoch (log : SpqrLog) : ℕ :=
  (log.sent.filterMap spqrPos).foldl (fun m p => max m p.1) 0

/-- Largest message index among committed receives at header epoch `E` (`0` if none). -/
def SpqrLog.recvCtr (log : SpqrLog) (E : ℕ) : ℕ :=
  ((log.recvd.filterMap spqrPos).filter (·.1 = E)).foldl (fun m p => max m p.2) 0

/-- SPQR symmetric-chain acceptance window (DEV-SPQR7): checks epoch retention
(`maxSendEpoch ≤ E + 1`), forward-jump cap `25000`, out-of-order window `2000`, and non-replay
against `log`. -/
def spqrWindowOk (log : SpqrLog) (pqMsg : List (BitVec 8)) : Bool :=
  match spqrPos pqMsg with
  | none => true
  | some (E, i) =>
    if E = 0 then true
    else
      let ctr := log.recvCtr E
      decide (log.maxSendEpoch ≤ E + 1) && decide (1 ≤ i) && decide (i ≠ ctr)
        && decide (ctr < i → i - ctr ≤ 25000) && decide (i < ctr → ctr ≤ i + 2000)
        && !(log.recvd.filterMap spqrPos).contains (E, i)

/-- Combined correctness window requiring `SM.mustLibsignal` (DEV-LS6) and `spqrWindowOk`
(DEV-SPQR7) on parsed ciphertexts. -/
def mustLibsignalSpqr {Msg : Type} (codec : SignalMessageProtoCodec)
    (s : SM.GameState (GhostState (PQ × SpqrLog)) Msg (List (BitVec 8))) (P : Party)
    (r : SM.Record Msg (List (BitVec 8))) : Bool :=
  SM.mustLibsignal s P r &&
    match SignalMessage.tryFrom codec r.ct with
    | .ok m => spqrWindowOk (s.st P).session.pqRatchetState.2 m.pqRatchet
    | .error _ => true

end LibsignalSession

/-! ## Honest-correctness game -/

namespace LibsignalSM.Corr

open LibsignalSession HKDF

variable {PQ PQC : Type}

def spqrDir : Party → SpqrDirection
  | .A => .a2b
  | .B => .b2a

/-- State of `spqrGame`: per-party logged SPQR state, chronological honest sends, and win flag. -/
structure SpqrGameState (PQ : Type) where
  st : Party → PQ × SpqrLog
  sent : List (Party × List (BitVec 8) × Salt)
  win : Bool

/-- Executes an honest SPQR send for `P`, setting `win` on panic or `none` (DEV-LS17). -/
def spqrSendStep (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party) (r : PQC) :
    Option (List (BitVec 8) × Salt) × SpqrGameState PQ :=
  if s.win then (none, s) else
  if S.withLog.sendPanics (s.st P) r then (none, { s with win := true }) else
  match S.withLog.send (s.st P) r with
  | none => (none, { s with win := true })
  | some (st', salt, msg) =>
    (some (msg, salt), { s with st := Function.update s.st P st', sent := s.sent ++ [(P, msg, salt)] })

/-- Delivers recorded send `j` to `P`, setting `win` on panic, in-window rejection, or salt
mismatch. -/
def spqrDeliverStep (S : Spqr PQ PQC) (s : SpqrGameState PQ) (P : Party) (j : ℕ) (commit : Bool) :
    Option Salt × SpqrGameState PQ :=
  if s.win then (none, s) else
  match s.sent[j]? with
  | none => (none, s)
  | some (Q, msg, salt) =>
    if Q ≠ P.other then (none, s) else
    if S.withLog.recvPanics (s.st P) msg then (none, { s with win := true }) else
    let inW := spqrWindowOk (s.st P).2 msg
    match S.withLog.recv (s.st P) msg with
    | .error _ => (none, { s with win := inW })
    | .ok (st', salt') =>
      let s' := if commit then { s with st := Function.update s.st P st' } else s
      (some salt', { s' with win := decide (salt' ≠ salt) })

abbrev SpqrSpec (PQ : Type) :=
  (Party →ₒ Option (List (BitVec 8) × Salt))
  + ((Party × ℕ × Bool) →ₒ Option Salt)
  + (Party →ₒ (PQ × SpqrLog))

abbrev SpqrAdversary (PQ : Type) := OracleComp (unifSpec + SpqrSpec PQ) Unit

def spqrSendImpl [SampleableType PQC] (S : Spqr PQ PQC) :
    QueryImpl (Party →ₒ Option (List (BitVec 8) × Salt)) (StateT (SpqrGameState PQ) ProbComp) :=
  fun P => do
    let r ← ($ᵗ PQC : ProbComp PQC)
    modifyGet fun s => spqrSendStep S s P r

def spqrDeliverImpl (S : Spqr PQ PQC) :
    QueryImpl ((Party × ℕ × Bool) →ₒ Option Salt) (StateT (SpqrGameState PQ) ProbComp) :=
  fun ⟨P, j, commit⟩ => modifyGet fun s => spqrDeliverStep S s P j commit

def spqrCorrImpl : QueryImpl (Party →ₒ (PQ × SpqrLog)) (StateT (SpqrGameState PQ) ProbComp) :=
  fun P => do
    let s ← get
    return s.st P

def spqrImpl [SampleableType PQC] (S : Spqr PQ PQC) :
    QueryImpl (SpqrSpec PQ) (StateT (SpqrGameState PQ) ProbComp) :=
  spqrSendImpl S + spqrDeliverImpl S + spqrCorrImpl (PQ := PQ)

/-- Honest-traffic SPQR correctness game initialized from a uniform 256-bit key. -/
def spqrGame [SampleableType PQC] (S : Spqr PQ PQC) (A : SpqrAdversary PQ) : ProbComp Bool := do
  let k ← ($ᵗ BitVec 256 : ProbComp (BitVec 256))
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (SpqrGameState PQ) ProbComp) + spqrImpl S
  let (_, s) ← (simulateQ impl A).run ⟨fun P => S.withLog.init (spqrDir P) k, [], false⟩
  return s.win

def isSpqrSend : ℕ ⊕ ((Party ⊕ (Party × ℕ × Bool)) ⊕ Party) → Bool
  | .inr (.inl (.inl _)) => true
  | _ => false

/-- `A` makes at most `q` `send` queries in `spqrGame`. -/
def SpqrSendsAtMost (A : SpqrAdversary PQ) (q : ℕ) : Prop :=
  A.IsQueryBoundP (fun t => isSpqrSend t = true) q

/-- Honest correctness of SPQR within `spqrWindowOk` (DEV-SPQR7; cf. `SpqrOffCorrect`, DEV-LS24):
any adversary making at most `q` sends without injections or chosen send coins (DEV-LS35) triggers
`win` in `spqrGame` with probability at most `ε` (accounting for ML-KEM decryption failures,
DEV-SPQR6). -/
def SpqrHonestCorrect [SampleableType PQC] (S : Spqr PQ PQC) (q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A : SpqrAdversary PQ, SpqrSendsAtMost A q → 𝒟[spqrGame S A] {true} ≤ ε

end LibsignalSM.Corr
end CryptoGames
