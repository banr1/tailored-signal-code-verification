/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import Computational.Proofs.CryptoGames.FSAEAD.HybridProofDefs

/-!
# Parameterized Hybrid Oracles, Runs, and Chain-PRG Reduction

Sender oracles (`transmitHWith`, `challengeHWith`), full oracle implementation (`oraclesWith`,
`implWith`), ambient hybrid runner (`hRunWith`, `hybridA`), cumulative chain-PRG reduction, and
tightened hybrid slot count (`slotCount`).
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
variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- Hybrid `transmit` oracle. -/
def transmitHWith (q : AD × M) : StateT St m (Option (ℕ × C)) := do
  let st ← getH
  if st.ended then pure none else do
  let i := st.lastSentIdx + 1
  genUpTo G P D i
  let e ← encIdxWith ideal ae P ops i q.1 q.2
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, q.2, (i, e)⟩ :: st.inTransit }
  pure (some (i, e))

/-- Hybrid `challenge` oracle. -/
def challengeHWith (q : AD × M × M) : StateT St m (Option (ℕ × C)) := do
  let st ← getH
  if st.ended || st.senderCorruptedAt.isSome then pure none else do
  let i := st.lastSentIdx + 1
  let msg := if st.b then q.2.2 else q.2.1
  genUpTo G P D i
  let e ← encIdxWith ideal ae P ops i q.1 msg
  modifyH fun st =>
    { st with lastSentIdx := i, inTransit := ⟨i, q.1, msg, (i, e)⟩ :: st.inTransit,
              challengesInTransit := i :: st.challengesInTransit }
  pure (some (i, e))

/-- Combined FS-AEAD game oracles for the hybrid game. -/
def oraclesWith :
    QueryImpl (spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M (ℕ × C))
      (StateT St m) :=
  (transmitHWith ideal ae G P D ops : QueryImpl _ _)
    + (challengeHWith ideal ae G P D ops : QueryImpl _ _)
    + (corruptSenderH (m := m) (AD := AD) (M := M) (C := C) G P :
        QueryImpl (Unit →ₒ Option (RatchetSenderState CK)) (StateT St m))
    + (corruptReceiverH (m := m) (AD := AD) (M := M) (C := C) (MK := MK) G P :
        QueryImpl (Unit →ₒ Option (RatchetSenderState CK × RatchetReceiverState CK MK))
          (StateT St m))
    + (deliverH ae G maxSkip P D ops : QueryImpl _ _)
    + (injectH ae G maxSkip P D ops : QueryImpl _ _)

/-- Full adversary query implementation (coins plus hybrid game oracles). -/
def implWith : QueryImpl (unifSpec + spec (RatchetSenderState CK) (RatchetReceiverState CK MK) AD M
    (ℕ × C)) (StateT St m) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St m)
    + oraclesWith ideal ae G maxSkip P D ops

end Oracles
section Games
variable [SampleableType MK] [SampleableType CK] [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ideal : ℕ × AD → ProbComp C)
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Runs a hybrid game from initial slot `sl` in ambient monad `m` and projects output via `hOut`. -/
def hRunWith {m : Type → Type} [Monad m] [MonadLiftT ProbComp m] (P : Params)
    (D : ℕ → ProbComp (CK × MK))
    (ops : Option (SpecialOps AD M C m))
    (A : RatchetAdversary CK MK AD M C) (sl : Slot CK MK) : m Bool := do
  let b ← (liftM ($ᵗ Bool : ProbComp Bool) : m Bool)
  let z ← (simulateQ (implWith ideal ae G maxSkip P D ops) A).run (hInit b sl)
  pure (hOut P.la z)

/-- Hybrid `A_k` with positions `< k` randomized and uncompromised indices `≤ k` ideal. -/
def hybridA (k : ℕ) (la : Bool) (A : RatchetAdversary CK MK AD M C) : ProbComp Bool :=
  hRunWith ideal ae G maxSkip (hp k k la) (DG G) none A .unknown

/-- PRG reduction at cumulative chain step `j` with `t = 0` (message-key slots kept real). -/
def cumulativeChainPrgReduction (j : ℕ) (A : RatchetAdversary CK MK AD M C) :
    PRGScheme.PRGAdversary (CK × MK) := fun mt =>
  hRunWith ideal ae G maxSkip (hp (j / 2) 0 (isLookaheadHop j)) (DG G)
    (none : Option (SpecialOps AD M C ProbComp)) A (.mat (j / 2) mt)

end Games
section Uniform
variable [SampleableType MK] [SampleableType CK] [SampleableType C]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

end Uniform

/-- Total active hybrid slots `2 * q + (maxSkip + 1)` (`q` main-chain plus `q + maxSkip + 1` lookahead-chain steps). -/
def slotCount (maxSkip q : ℕ) : ℕ :=
  2 * q + (maxSkip + 1)

end CryptoGames.FSAEAD.Thm5
