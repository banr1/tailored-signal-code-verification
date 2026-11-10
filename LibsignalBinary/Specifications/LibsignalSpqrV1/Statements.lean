/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import GeneratedLean.LibsignalSessionObj

/-!
# SPQR V1: binary refinement statements

**Checked by Lean.**

States the binary-level specifications of `spqr::send::<HookRng>` (`SpqrSendV1Stmt`) and
`spqr::recv` (`SpqrRecvV1Stmt`) in libsignal's ARM64 image against `spqrV1 C.F K` and
`spqrV1Recv C.F K` (`Model.lean`), together with the framed Triple Ratchet entry-point statements
`OtrEncryptV1RunStmt`, `TryDecryptV1RunStmt`, and `RecordDecryptV1RunStmt` (`Hooks.lean`,
`Entries.lean`).

## DEV-SPQR1 (PMULL)
**DEV-SPQR1 (machine model): `TokenInit`, spqr's PMULL detection has run and found no PMULL.**
The ARM64 engine has no `PMULL` instruction, so `spqrSendSpecT`, `spqrRecvSpecExactKeyBounded`,
`otrEncryptSpecT`, `tryDecryptSpecT`, and `recordDecryptSpecT` frame `TokenInit`, selecting
`unaccelerated::mul` in $\mathrm{GF}(2^{16})$.

## DEV-SPQR3 (input sizes)
**DEV-SPQR3 (machine model): the state is shorter than `2^32` bytes, the message than `2^40`.**
`spqrSendSpecT` and `spqrRecvSpecExactKeyBounded` require the serialized state length to be `< 2^32`
and (for recv) the message length to be `< 2^40`, ruling out `RawVec` `capacity_overflow` panics
(`2 * cap * stride >= 2^63`). On decrypt, `< 2^40` comes from `signalMessageAt`; the state bound is
carried by `otrEncryptSpecT`, `tryDecryptSpecT`, and `recordDecryptSpecT` and discharged at public
entries via `RecordPqStateLengthBelow2Pow32` (`loadSessionSpecPqStateLengthBound` in `Entries.lean`).

## DEV-SPQR4 (recv stack non-wrap)
**DEV-SPQR4 (machine model): the recv stack does not wrap through address 0.**
`spqrRecvSpecExactKeyBounded` requires `spqrRecvStack ≤ sp` so stack-allocated `VersionNegotiation`
pointers (`sp - 4992`, `sp - 4640`) passed as `Option<&VersionNegotiation>` to `spqr::chain_from`
are non-null; discharged at decrypt integration from `rootStack = 2^18 ≤ sp`.

## DEV-SPQR5 (send random tape)
**DEV-SPQR5 (machine model): `spqr::send` has at least 64 random-tape bytes.**
`spqrSendSpecT` and `otrEncryptSpecT` require `64 ≤ x.rest.length`. Whereas `rngFillHook` zero-pads
a short tape and returns normally, the model's `generate` (64 bytes) and `encaps1` (32 bytes) return
`rngExhausted`; 64 unread tape bytes ensure a single `States::send` call never hits `rngExhausted`.

## DEV-SPQR2 (recv key type)
**DEV-SPQR2 (libsignal): `spqr::recv` can return the key `Some([])`; the recv statement uses the
exact key type.**
In `spqr::recv`'s version-negotiation `Ordering::Greater` branch (`src/lib.rs:401–419`) with
`msg.index = 0`, `Chain::recv_key(0, 0)` returns `Ok(vec![])` wrapped unconditionally in `Some`
without the `is_empty()` filter of the V1 path (`src/lib.rs:478–482`). `SpqrRecvV1Stmt` therefore
targets `spqrRecvSpecExactKeyBounded` over `SpqrRecvModel` (`Option (List (BitVec 8))`). Under
`SeedsLen32` (DEV-LS9), `MessageKeyGenerator::generate_keys` uses the key only as an HKDF salt where
`Some(&[])` and `None` agree (DEV-LS25); `toSpqrModel.recv` maps `some []` via `recvKeyToSalt?` to
`none`, and `spqrRecvSpecXT_imp_spqrRecvSpec` bridges `SpqrRecvV1Stmt` to `spqrRecvSpecT`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr

/-- `spqrSendSpec` framed with `TokenInit` (DEV-SPQR1), state length `< 2^32` (DEV-SPQR3), and
`64 ≤ x.rest.length` (DEV-SPQR5). -/
def spqrSendSpecT (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image) :
    Spec SendCall :=
  { spqrSendSpec A ctl S img with
    pre := fun x s =>
      ⌜x.st.bytes.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (spqrSendSpec A ctl S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (spqrSendSpec A ctl S img).post x s0 sf }

/-! ## DEV-SPQR2: recv contract with exact key type -/

/-- Layout of `spqr::MessageKey = Option<Vec<u8>>` at `a` (24 bytes): `noneCap` niche on `none`, or
owned `vecU8` on `some k`. -/
def optKeyBytesAt (A : RustAlloc) (a : BitVec 64) : Option (List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 16
  | some k => vecU8 A a k

/-- Layout of `Result<spqr::Recv, spqr::Error>` at `r` (48 bytes) with exact `Option (List (BitVec 8))`
message key (`optKeyBytesAt`). -/
def recvResultExactKeyAt (A : RustAlloc) (r : BitVec 64) :
    Except Bool (List (BitVec 8) × Option (List (BitVec 8))) → SepProp
  | .ok (st', key) => vecU8 A r st' ∗ optKeyBytesAt A (r + 24#64) key
  | .error sd =>
    (r ↦₆₄ errTag) ∗ (∃∗ d : BitVec 8, ⌜(d = 0#8 ↔ sd = true)⌝ ∗ ((r + 8#64) ↦₈ d)) ∗
      memRegion (r + 9#64) 39

/-- `spqrRecvSpec` over `SpqrRecvModel` using `recvResultExactKeyAt` (DEV-SPQR2). -/
def spqrRecvSpecExactKey (A : RustAlloc) (R : SpqrRecvModel) (img : Obj.Image) :
    Spec (VecArg × VecArg × BitVec 64) :=
  Spec.inImage
    { pre := fun (st, msg, ret) s =>
        ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
          st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ logOff img ∗ A.pool ∗ stackAt s.sp spqrRecvStack
      post := fun (st, msg, ret) s0 sf =>
        ⌜sf.trace = s0.trace ∧ ¬ R.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
          recvResultExactKeyAt A ret (R.recv st.bytes msg.bytes) ∗
          logOff img ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
      onPanic := fun (st, msg, _) s0 sf =>
        ⌜(allocFailedIn s0 sf ∨ R.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap }
    img

/-- `spqrRecvSpecExactKey` framed with `TokenInit` (DEV-SPQR1), state `< 2^32` and message `< 2^40`
(DEV-SPQR3), and `spqrRecvStack ≤ sp` (DEV-SPQR4). -/
def spqrRecvSpecExactKeyBounded (A : RustAlloc) (R : SpqrRecvModel) (img : Obj.Image) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvSpecExactKey A R img with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        TokenInit img ∗ (spqrRecvSpecExactKey A R img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (spqrRecvSpecExactKey A R img).post x s0 sf }

/-- `spqrRecvSpec` framed with `TokenInit` (DEV-SPQR1), state `< 2^32` and message `< 2^40`
(DEV-SPQR3), and `spqrRecvStack ≤ sp` (DEV-SPQR4). -/
def spqrRecvSpecT (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) :
    Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvSpec A S img with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        TokenInit img ∗ (spqrRecvSpec A S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (spqrRecvSpec A S img).post x s0 sf }

theorem optKeyBytesAt_entails_optKeyRecvAt (A : RustAlloc) (a : BitVec 64)
    {key : Option (List (BitVec 8))} {salt : CryptoGames.HKDF.Salt}
    (h : recvKeyToSalt? key = some salt) :
    optKeyBytesAt A a key ⊢ spqrRecvKeyAt A a salt := by
  cases key with
  | none =>
    injection h with h; subst h
    refine Entails.trans ?_ (Entails.sepExists_intro true)
    exact Entails.refl _
  | some k =>
    cases k with
    | nil =>
      injection h with h; subst h
      refine Entails.trans ?_ (Entails.sepExists_intro false)
      exact Entails.refl _
    | cons b bs =>
      have hne : some (b :: bs) ≠ some [] := nofun
      rw [recvKeyToSalt?_of_ne hne] at h
      dsimp only [messageKeyToSalt?] at h
      split at h
      · injection h with h; subst h
        exact Entails.refl _
      · contradiction

theorem recvResultAtX_entails_recvResultAt (A : RustAlloc) (ret : BitVec 64)
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem)
    (stBytes msgBytes : List (BitVec 8)) :
    recvResultExactKeyAt A ret ((spqrV1Recv F K).recv stBytes msgBytes) ⊢
      spqrRecvResultAt A ret ((spqrV1 F K).recv stBytes msgBytes) := by
  rw [spqrV1Recv_eq, spqrV1_eq]
  dsimp only [toSpqrRecvModel, toSpqrModel]
  cases h : recv (spqrDeps F K) (spqrHkdfWith F) stBytes msgBytes with
  | ok r =>
    have hv := recv_key_valid (spqrDeps F K) F stBytes msgBytes h
    cases hsalt : recvKeyToSalt? r.key with
    | none => simp [hsalt] at hv
    | some salt =>
      simp only [hsalt, recvResultExactKeyAt, spqrRecvResultAt]
      exact sepConj_mono_right (optKeyBytesAt_entails_optKeyRecvAt A (ret + 24#64) hsalt)
  | error e =>
    cases e <;> exact Entails.refl _

/-- Bridge theorem (DEV-SPQR2): `spqrRecvSpecExactKeyBounded` for `spqrV1Recv F K` implies `spqrRecvSpecT`
for `spqrV1 F K` because `spqrRecvResultAt` widens `spqrRecvKeyAt` to accept `Some([])` on `.none`. -/
theorem spqrRecvSpecXT_imp_spqrRecvSpec (prog : Program) (entry_pc : BitVec 64)
    (A : RustAlloc) (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) (img : Obj.Image)
    (h : subroutine_ok prog entry_pc (spqrRecvSpecExactKeyBounded A (spqrV1Recv F K) img)) :
    subroutine_ok prog entry_pc (spqrRecvSpecT A (spqrV1 F K) img) := by
  have heq : (spqrV1Recv F K).recvPanics = fun st msg => (spqrV1 F K).recvPanics st msg = true := by
    rw [spqrV1Recv_eq, spqrV1_eq]; rfl
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun (st, msg, ret) R s0 sf hpost => ?_)
    (fun (st, msg, ret) R s0 sf hpan => ?_) (fun _ _ _ _ _ he => he)
  · dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecT, spqrRecvSpecExactKey, spqrRecvSpec, Spec.inImage] at hpost ⊢
    rw [heq] at hpost
    refine Satisfies.mono ?_ hpost
    refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))
    exact sepConj_mono_right (sepConj_mono_left
      (recvResultAtX_entails_recvResultAt A ret F K st.bytes msg.bytes))
  · dsimp only [spqrRecvSpecExactKeyBounded, spqrRecvSpecT, spqrRecvSpecExactKey, spqrRecvSpec, Spec.inImage] at hpan ⊢
    rwa [heq] at hpan

/-- Binary refinement statement for `spqr::send::<HookRng>` against `spqrV1 C.F K`. -/
def SpqrSendV1Stmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrSendName)
      (spqrSendSpecT A ctl (spqrV1 C.F K) img)

/-- Binary refinement statement for `spqr::recv` against `spqrV1Recv C.F K` (DEV-SPQR2). -/
def SpqrRecvV1Stmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv C.F K) img)

/-- `otrEncryptSpec` framed with `TokenInit` (DEV-SPQR1), `pqrState.length < 2^32` (DEV-SPQR3),
and `64 ≤ x.rest.length` (DEV-SPQR5). -/
def otrEncryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  { otrEncryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.ot.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
        TokenInit img ∗ (otrEncryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (otrEncryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- `tryDecryptSpec` framed with `TokenInit` (DEV-SPQR1) and `pqRatchetState.length < 2^32`
(DEV-SPQR3). -/
def tryDecryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit img ∗ (tryDecryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf => TokenInit img ∗ (tryDecryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- `recordDecryptSpec` framed with `TokenInit` (DEV-SPQR1) and `pqRatchetState.length < 2^32`
(DEV-SPQR3). -/
def recordDecryptSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec RecordDecryptGhost :=
  { recordDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        TokenInit img ∗ (recordDecryptSpec C A ctl uuidParse S img).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗ (recordDecryptSpec C A ctl uuidParse S img).post x s0 sf }

/-- Binary refinement statement for `OutgoingTripleRatchet::encrypt` with `spqrV1 C.F K`. -/
def OtrEncryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img otrEncryptName)
      (otrEncryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- Binary refinement statement for `try_decrypt_with_state` with `spqrV1 C.F K`. -/
def TryDecryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      (tryDecryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

/-- Binary refinement statement for `try_decrypt_from_record` with `spqrV1 C.F K`. -/
def RecordDecryptV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (spqrV1 C.F K) abs → SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    region_ok (tripleRatchetProg img C ctl abs) (recordRegionEntry img) (recordRegionExit img)
      (recordDecryptSpecT C A ctl uuidTryParse (spqrV1 C.F K) img)

end CryptoVerification.LibsignalSpqrV1

