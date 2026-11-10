/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import GeneratedLean.LibsignalSessionObj

/-!
# CLI SPQR V1 Specifications and Verification Statements

Specializes the CLI Triple Ratchet specifications with `TokenInit` framed (DEV-SPQR1), `2^32`
SPQR state-length bounds (DEV-SPQR3), and 64-byte random-tape bounds (DEV-SPQR5), and states the
SPQR V1 verification obligations for `spqr::send`, `OTR::encrypt`, `try_decrypt_with_state`, and
`try_decrypt_from_record` (pairing with the DEV-SPQR2 receive model `SpqrRecvModel` / `spqrV1Recv`
in `Model.lean`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr

/-- `CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec` with `TokenInit` framed (DEV-SPQR1), the state shorter than `2^32` bytes
(DEV-SPQR3), and at least 64 random-tape bytes left (DEV-SPQR5). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img with
    pre := fun x s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec A ctl S img).post x s0 sf }

/-- **Headline (send).** The in-image `spqr::send::<HookRng>` meets `CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT` (`CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec`
with `TokenInit` framed, DEV-SPQR1, and the size and random-tape bounds, DEV-SPQR3 / DEV-SPQR5) for
the SPQR V1 model, on every state, from the hook contracts (no `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk` hypothesis). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.SpqrSendV1Stmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalSpqrV1.spqrSendSpecT A ctl (spqrV1 C.F K) img)

/-- `CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec` with `TokenInit` framed (DEV-SPQR1), the SPQR send state shorter than `2^32`
bytes (DEV-SPQR3), and at least 64 bytes on the random tape (DEV-SPQR5). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.ot.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec` with `TokenInit` framed (DEV-SPQR1) and the SPQR recv state shorter than
`2^32` bytes (DEV-SPQR3; `x.msg.pqRatchet.length < 2^40` and `rootStack ≤ s.sp.toNat` are already
in `CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec.pre`). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- `CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec` with `TokenInit` framed (DEV-SPQR1) and the SPQR recv state shorter than
`2^32` bytes (DEV-SPQR3). -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec RecordDecryptGhost :=
  { CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- **Encrypt, SPQR V1 (without `CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendOk`).** For the SPQR V1 model, `OTR::encrypt`
meets `CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT` from `TripleRatchetHooks` and `SpqrHooks` via `CryptoVerification.Cli.LibsignalSpqrV1.SpqrSendV1Stmt`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.OtrEncryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- **Decrypt, SPQR V1 (without `SpqrRecvOk`).** For the SPQR V1 model, `try_decrypt_with_state`
meets `CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT` from `TripleRatchetHooks` and `SpqrHooks` via `SpqrRecvV1Stmt` and
`spqrRecvSpecXT_imp_spqrRecvSpec`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.TryDecryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- **Decrypt from a record, SPQR V1 (without `SpqrRecvOk`).** For the SPQR V1 model, the
`try_decrypt_from_record` region meets `CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT` from `TripleRatchetHooks` and
`SpqrHooks`. -/
def _root_.CryptoVerification.Cli.LibsignalSpqrV1.RecordDecryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
      (CryptoVerification.Cli.LibsignalSpqrV1.recordDecryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

end CryptoVerification.LibsignalSpqrV1
