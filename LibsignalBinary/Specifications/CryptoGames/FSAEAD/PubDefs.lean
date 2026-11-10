/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.SM.Game

/-!
# Public message components and AD classes (libsignal adapters for FS-AEAD)

**Checked by Lean.** No theorem of `Computational/Theorems/` uses the definitions of this file.
See `Computational/docs/TRUSTED_BASE.md`.

Adapters moving a plaintext's public authenticated header component `Pub` into the associated data
of an AEAD (`AEADScheme.movePubPartToAD`) and of an FS-AEAD adversary (`FSAEAD.pubRed`, DEV-FS19);
adversary restrictions to equal challenge public parts and single AD classes (DEV-FS20) live in
`Computational/Proofs/CryptoGames/FSAEAD/PubProofDefs.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

namespace AEADScheme

variable {K AD Pub M C : Type}

/-- AEAD with AD `AD` and plaintext `Pub × M` obtained from `ae : AEADScheme K (AD × Pub) M C` by
moving `Pub` into the AD on encryption and recovering it from the ciphertext via `pubOf`.

**DEV-FS19 (libsignal): a public, authenticated part of the message.** libsignal MACs clear-text
fields (`previous_counter` and the SPQR message and salt) alongside `(t, T)`; modeling them as `Pub`
carried in the underlying AEAD's AD restricts FS-AEAD challenges to agree on `Pub`
(`FSAEAD.EqualPubChallenges`). -/
def movePubPartToAD (ae : AEADScheme K (AD × Pub) M C) (pubOf : C → Option Pub) :
    AEADScheme K AD (Pub × M) C where
  enc k a pm := ae.enc k (a, pm.1) pm.2
  dec k a c :=
    match pubOf c with
    | none => none
    | some p => (ae.dec k (a, p) c).map fun m => (p, m)

end AEADScheme

namespace FSAEAD

variable {SS RS AD Pub M C : Type}

/-- Attach public part `p` to an accepted `ReceiveResult`. -/
def withPub {Pub M : Type} (p : Pub) : ReceiveResult M → ReceiveResult (Pub × M)
  | .rejected => .rejected
  | .accepted i m => .accepted i (m.map fun m => (p, m))

/-- Oracle implementation for `pubRed`, translating queries with messages `Pub × M` and AD `AD` to
the FS-AEAD game with AD `AD × Pub` and messages `M` using `pubOf` on ciphertexts and tracking
whether `corruptReceiver` has ended the game. -/
def pubRedImpl {SS RS AD Pub M C : Type} (pubOf : C → Option Pub) :
    QueryImpl (unifSpec + spec SS RS AD (Pub × M) C)
      (StateT Bool (OracleComp (unifSpec + spec SS RS (AD × Pub) M C))) := fun q => match q with
  | .inl n => StateT.lift (query (spec := unifSpec + spec SS RS (AD × Pub) M C) (.inl n))
  | .inr (.inl (.inl (.inl (.inl (.inl ⟨a, pm⟩))))) => StateT.lift
    (transmitQuery (SenderState := SS) (ReceiverState := RS) (a, pm.1) pm.2)
  | .inr (.inl (.inl (.inl (.inl (.inr ⟨a, pm₀, pm₁⟩))))) => StateT.lift
    (challengeQuery (SenderState := SS) (ReceiverState := RS) (a, pm₀.1) pm₀.2 pm₁.2)
  | .inr (.inl (.inl (.inl (.inr _)))) => StateT.lift
    (corruptSenderQuery (ReceiverState := RS) (AssocData := AD × Pub) (Message := M) (Ciphertext := C))
  | .inr (.inl (.inl (.inr _))) => do
    let r ← StateT.lift (corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
      (AssocData := AD × Pub) (Message := M) (Ciphertext := C))
    if r.isSome then set true
    return r
  | .inr (.inl (.inr ⟨a, c⟩)) =>
    match pubOf c with
    | none => return none
    | some p => StateT.lift do
      let r ← deliverQuery (SenderState := SS) (ReceiverState := RS) (Message := M) (a, p) c
      return r.map (withPub p)
  | .inr (.inr ⟨a, c⟩) =>
    match pubOf c with
    | none => do
      let ended ← get
      return if ended then none else some .rejected
    | some p => StateT.lift do
      let r ← injectQuery (SenderState := SS) (ReceiverState := RS) (Message := M) (a, p) c
      return r.map (withPub p)

/-- **The pub-moving reduction**: `A` run with `pubRedImpl`, starting with "not ended". -/
def pubRed {SS RS AD Pub M C : Type} (pubOf : C → Option Pub) (A : Adversary SS RS AD (Pub × M) C) :
    Adversary SS RS (AD × Pub) M C :=
  (simulateQ (pubRedImpl pubOf) A).run' false

end FSAEAD

namespace SM

variable {St Msg Coins C Pub : Type}

end SM

end CryptoGames
