/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement

/-!
# Single-Cut Collision Excuses and Move-Level Model Target

Defines single-cut hardware-trace collision excuse predicates (`PrefixGhosts`, `WhisperExcused`,
`PreKeyExcused`, `CollisionAt`) and the move-level intermediate target `CompRefinesCliModelMoves`.
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement

open DY DY.Comparse DY.Libsignal
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Rust

/-- Ghosts sharing `g.σ` that explain the hardware trace prefix `τ` alongside `ms`. -/
def PrefixGhosts (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (g : Ghost) (ms : List Move) (τ : List MachineEvent) : Set Ghost :=
  {g' | g'.σ = g.σ ∧ MatchedPrefix interpretation r S who g' ms τ}

/-- States that an accepted whisper message body `b` after prefix `τ₁` requires a cryptographic
collision under every collision-free explanation of `τ₁`. -/
def WhisperExcused (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent)
    (b : HwBytes) : Prop :=
  (∃ t, t ∈ recvRepresentations interpretation r S g ms b) ∧
    ∀ g' ms', ExplainsMoves interpretation r S who ok g' ms' τ₁ →
      ¬ ReadCollision interpretation r S g' ms' τ₁ →
      let reps := recvRepresentations interpretation r S g' ms' b
      let accepts := ModelAcceptsTermAfterCoinSplit interpretation r S who ok g' ms' τ₁ e τ₂
      (∀ t ∈ reps, RecvCollision interpretation r S g' ms' t ∨
          ReselectCollision interpretation r S g' ms' t) ∨
        ((∃ t ∈ reps, accepts t) ∧
          ∀ t ∈ reps, accepts t → RecvCollision interpretation r S g' ms' t)

/-- States that a pre-key message `p` received as `b` after prefix `τ₁` either has a
`KyberMismatch` or triggers a session-start collision or implicit rejection under every
collision-free explanation of `τ₁`. -/
def PreKeyExcused (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (g : Ghost) (ms : List Move)
    (τ₁ : List MachineEvent) (b : HwBytes) (p : PreKeyFields) : Prop :=
  (∃ x, x ∈ preKeyRepresentations interpretation r S g ms b) ∧
    (KyberMismatch interpretation r p ∨
      ∀ g' ms', ExplainsMoves interpretation r S who ok g' ms' τ₁ →
        ¬ ReadCollision interpretation r S g' ms' τ₁ →
        ∀ x ∈ preKeyRepresentations interpretation r S g' ms' b,
          BobSessionStartCollidesOrImplicitRejects interpretation r S g' ms' p x)

/-- Hardware trace `τ` splits at an explained prefix `τ₁` followed by a `recv` or `pt` event
that forces a cryptographic collision. -/
def CollisionAt (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool) (τ : List MachineEvent) : Prop :=
  ∃ (τ₁ : List MachineEvent) (e : MachineEvent) (τ₂ : List MachineEvent) (g : Ghost)
    (ms : List Move),
    τ = τ₁ ++ (e :: τ₂) ∧
    ExplainsMoves interpretation r S who ok g ms τ₁ ∧
    let accepted := ∃ pt, (τ₂.filter fun e => eventKind e != .rng).head? = some (.accept pt)
    match e with
    | .recv (tag :: body) =>
      accepted ∧
      ((tag = wireWhisperTag ∧
          WhisperExcused interpretation r S who ok g ms τ₁ (.recv (tag :: body)) τ₂ body) ∨
       (∃ p, parsePreKeyWire (tag :: body) = some p ∧
          ((KnownBaseKey interpretation r S g ms p ∧
              WhisperExcused interpretation r S who ok g ms τ₁ (.recv (tag :: body)) τ₂
                p.message) ∨
           (¬ KnownBaseKey interpretation r S g ms p ∧
              PreKeyExcused interpretation r S who ok g ms τ₁ (tag :: body) p))))
    | .pt b =>
      let v := ptEntryOfNextEncrypt r ms
      let tr := runTraceMoves r ms
      EventMatchesEntry interpretation r S g (.pt b) v ∧
        ∀ g' ∈ PrefixGhosts interpretation r S who g ms τ₁,
          MemoCollisionOn interpretation r S g' (fun u => u.AttackerKnows tr) tr (runVis r ms)
            v.terms v.terms
    | _ => False

end DY.Libsignal.Composed.Refinement

namespace DY.Libsignal.Composed.Refinement.Cli

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement
open CryptoVerification.SignalSession (Inputs Outcome)

/-- Move-level CLI refinement target instantiating `CompRefinesCliMoves` with `ModelAgree` and
`PqModelRel`. -/
def CompRefinesCliModelMoves : Prop :=
  CompRefinesCliMoves ModelAgree PqModelRel

end DY.Libsignal.Composed.Refinement.Cli
