/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import Symbolic.Specifications.Concrete.ExternInterpretation
public import Symbolic.Proofs.SpecLemmas.ImageSymbolsProofDefs

/-!
# Hook-Parameterized SPQR V1 Authentication and Model Instances

Parameterizes SPQR V1 header and ciphertext authentication over an abstract `HmacFn` and
external ML-KEM hooks (`mlkemOf`), proving agreement with `spqrAuthApi` and `spqrDeps` when
instantiated with `hmacFnOfSha F`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.SHARED.HookAuth

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (
  mlkem768FromSeedSymbol mlkem768ValidatePkSymbol mlkem768Encaps1Symbol
  mlkem768Encaps2Symbol mlkem768DecapsSymbol libcruxHmacSymbol)

/-- Partial MAC function parameterizing SPQR header and ciphertext authentication. -/
abbrev HmacFn : Type := List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))

/-- Total SHA-256 HMAC instantiation of `HmacFn` from a compression function `F`. -/
def hmacFnOfSha (F : ShaCompress) : HmacFn :=
  fun k d => some (hmacWith F k d)

/-- `HmacFn` induced by `i : ExternInterpretation` at `libcruxHmacSymbol`. -/
def hmacFnOf (i : ExternInterpretation) : HmacFn :=
  fun key data => i libcruxHmacSymbol [key, data]

/-- Convert a byte list to a `List.Vector (BitVec 8) n`, padding with `0#8` or truncating to length `n`. -/
def bytesToVec (n : Nat) (bs : List (BitVec 8)) : List.Vector (BitVec 8) n :=
  ⟨(bs ++ List.replicate n 0#8).take n, by
    rw [List.length_take, List.length_append, List.length_replicate]
    omega⟩

/-- `MlKem` instance constructed from `i : ExternInterpretation`. -/
def mlkemOf (i : ExternInterpretation) : MlKem where
  keyPair seed := bytesToVec 2400 ((i mlkem768FromSeedSymbol [seed.toList]).getD [])
  validPk hdr ek := (i mlkem768ValidatePkSymbol [hdr, ek]).isSome
  encaps1 hdr rand :=
    match i mlkem768Encaps1Symbol [hdr, rand.toList] with
    | some o =>
        some (bytesToVec 960 (o.take 960),
              bytesToVec 2080 ((o.drop 960).take 2080),
              bytesToVec 32 (o.drop 3040))
    | none => none
  encaps2 es ek :=
    bytesToVec 128 ((i mlkem768Encaps2Symbol [es.toList, ek.toList]).getD [])
  decaps dk ct1 ct2 :=
    bytesToVec 32 ((i mlkem768DecapsSymbol [dk.toList, ct1.toList, ct2.toList]).getD [])

/-! ## Hook-Parameterized `Authenticator` Operations -/

/-- `Authenticator.macCt` parameterized by `mac : HmacFn`, returning the raw tag on `some tag`,
`.error (.site ...)` on `none`, and `.error hmacU32UnwrapPanic` when inputs exceed `2 ^ 32`. -/
def macCtWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    Except SpqrPanic Mac :=
  let data := Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct
  if self.macKey.length < 2 ^ 32 ∧ data.length < 2 ^ 32 then
    match mac self.macKey data with
    | some tag => .ok tag
    | none =>
      .error (.site "Authenticator::mac_ct: libcrux_hmac::hmac returned none")
  else
    .error hmacU32UnwrapPanic

@[simp]
theorem macCtWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    macCtWithMac (hmacFnOfSha F) self ep ct = self.macCt F ep ct := by
  unfold macCtWithMac Authenticator.macCt Authenticator.macCtUnchecked hmacFnOfSha
  dsimp only
  rw [List.take_of_length_le (by simp [Authenticator.macSize, length_hmacWith])]

/-- `Authenticator.macHdr` parameterized by `mac : HmacFn`, returning the raw tag on `some tag`,
`.error (.site ...)` on `none`, and `.error hmacU32UnwrapPanic` when inputs exceed `2 ^ 32`. -/
def macHdrWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    Except SpqrPanic Mac :=
  let data := Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr
  if self.macKey.length < 2 ^ 32 ∧ data.length < 2 ^ 32 then
    match mac self.macKey data with
    | some tag => .ok tag
    | none =>
      .error (.site "Authenticator::mac_hdr: libcrux_hmac::hmac returned none")
  else
    .error hmacU32UnwrapPanic

@[simp]
theorem macHdrWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    macHdrWithMac (hmacFnOfSha F) self ep hdr = self.macHdr F ep hdr := by
  unfold macHdrWithMac Authenticator.macHdr Authenticator.macHdrUnchecked hmacFnOfSha
  dsimp only
  rw [List.take_of_length_le (by simp [Authenticator.macSize, length_hmacWith])]

/-- `Authenticator.verifyCtError` parameterized by `mac : HmacFn`. -/
def verifyCtErrorWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch)
    (ct expectedMac : Bytes) : Except SpqrPanic (Except Error Unit) := do
  let computed ← macCtWithMac mac self ep ct
  let diff ← CryptoVerification.LibsignalSpqrV1.compare expectedMac computed
  return if diff != 0#8 then .error .macVerifyFailed else .ok ()

@[simp]
theorem verifyCtErrorWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
    verifyCtErrorWithMac (hmacFnOfSha F) self ep ct expectedMac =
      self.verifyCtError F ep ct expectedMac := by
  unfold verifyCtErrorWithMac Authenticator.verifyCtError Authenticator.verifyCt
  rw [macCtWithMac_hmacFnOfSha]
  cases self.macCt F ep ct with
  | error e => rfl
  | ok m =>
    dsimp [Bind.bind, Except.bind, Except.map]
    cases CryptoVerification.LibsignalSpqrV1.compare expectedMac m with
    | error e => rfl
    | ok diff =>
      dsimp [pure, Except.pure, Except.mapError, AuthError.toError]
      cases (diff != 0#8) <;> rfl

/-- `Authenticator.verifyHdrError` parameterized by `mac : HmacFn`. -/
def verifyHdrErrorWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch)
    (hdr expectedMac : Bytes) : Except SpqrPanic (Except Error Unit) := do
  let computed ← macHdrWithMac mac self ep hdr
  let diff ← CryptoVerification.LibsignalSpqrV1.compare expectedMac computed
  return if diff != 0#8 then .error .macVerifyFailed else .ok ()

@[simp]
theorem verifyHdrErrorWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
    verifyHdrErrorWithMac (hmacFnOfSha F) self ep hdr expectedMac =
      self.verifyHdrError F ep hdr expectedMac := by
  unfold verifyHdrErrorWithMac Authenticator.verifyHdrError Authenticator.verifyHdr
  rw [macHdrWithMac_hmacFnOfSha]
  cases self.macHdr F ep hdr with
  | error e => rfl
  | ok m =>
    dsimp [Bind.bind, Except.bind, Except.map]
    cases CryptoVerification.LibsignalSpqrV1.compare expectedMac m with
    | error e => rfl
    | ok diff =>
      dsimp [pure, Except.pure, Except.mapError, AuthError.toError]
      cases (diff != 0#8) <;> rfl

/-! ## Hook-Parameterized `AuthApi`, `SpqrApiDeps`, and SPQR Models -/

/-- `AuthApi` instance parameterized by `F : ShaCompress` for HKDF and `mac : HmacFn` for MACs. -/
def spqrAuthApiWithMac (F : ShaCompress) (mac : HmacFn := hmacFnOfSha F) : AuthApi where
  Authenticator := Authenticator
  new := fun rootKey ep => .ok (Authenticator.new F rootKey ep)
  update := fun auth ep k => .ok (auth.update F ep k)
  mac_hdr := fun auth ep hdr => macHdrWithMac mac auth ep hdr
  mac_ct := fun auth ep ct => macCtWithMac mac auth ep ct
  verify_hdr := fun auth ep hdr expectedMac => verifyHdrErrorWithMac mac auth ep hdr expectedMac
  verify_ct := fun auth ep ct expectedMac => verifyCtErrorWithMac mac auth ep ct expectedMac
  into_pb := Authenticator.intoPb
  from_pb := Authenticator.fromPb
  hkdf_to_vec := hkdfToVec F

@[simp]
theorem spqrAuthApiWithMac_hmacFnOfSha (F : ShaCompress) :
    spqrAuthApiWithMac F (hmacFnOfSha F) = spqrAuthApi F := by
  unfold spqrAuthApiWithMac spqrAuthApi
  simp

/-- `SpqrApiDeps` bundle parameterized by `F : ShaCompress`, `K : MlKem`, and `mac : HmacFn`. -/
def spqrDepsWithMac (F : ShaCompress) (K : MlKem) (mac : HmacFn := hmacFnOfSha F) : SpqrApiDeps where
  V1StatePB := V1State
  decodeState := fun bs =>
    match Proto.decodeState bs with
    | .ok st => .ok (pqRatchetStateToPb st)
    | .error _ => .error ()
  encodeState := fun st =>
    Proto.encodeState (pbToPqRatchetState st)
  States := States spqrPolyApi (spqrAuthApiWithMac F mac)
  statesFromPb := fun pb =>
    liftStatesResult (States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb)
  statesIntoPb := States.into_pb
  MessageV1 := Message spqrPolyApi
  statesSend := fun st tape =>
    match st.send K tape with
    | .ok (sOut, tape') => (.ok (sOut.msg, sOut.key, sOut.state), tape')
    | .error (.err e) => (.error (.err e), tape)
    | .error (.panic _) => (.error (.panic .v1), tape)
  statesRecv := fun st msg =>
    match st.recv K msg with
    | .ok rOut => .ok (rOut.key, rOut.state)
    | .error (.err e) => .error (.err e)
    | .error (.panic _) => .error (.panic .v1)
  msgSerialize := Message.serialize
  msgDeserialize := fun ep rem =>
    match Message.deserialize spqrPolyApi ep rem with
    | .ok m => .ok m
    | .error e => .error (.err e)
  msgEpoch := Message.epoch
  initV1Inner := fun dir authKey =>
    match dir with
    | .a2b =>
      match States.init_a spqrPolyApi (spqrAuthApiWithMac F mac) authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1
    | .b2a =>
      match States.init_b spqrPolyApi (spqrAuthApiWithMac F mac) authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1

private def spqrDepsOfAuth (auth : AuthApi) (K : MlKem) : SpqrApiDeps where
  V1StatePB := V1State
  decodeState := fun bs =>
    match Proto.decodeState bs with
    | .ok st => .ok (pqRatchetStateToPb st)
    | .error _ => .error ()
  encodeState := fun st =>
    Proto.encodeState (pbToPqRatchetState st)
  States := States spqrPolyApi auth
  statesFromPb := fun pb =>
    liftStatesResult (States.from_pb spqrPolyApi auth pb)
  statesIntoPb := States.into_pb
  MessageV1 := Message spqrPolyApi
  statesSend := fun st tape =>
    match st.send K tape with
    | .ok (sOut, tape') => (.ok (sOut.msg, sOut.key, sOut.state), tape')
    | .error (.err e) => (.error (.err e), tape)
    | .error (.panic _) => (.error (.panic .v1), tape)
  statesRecv := fun st msg =>
    match st.recv K msg with
    | .ok rOut => .ok (rOut.key, rOut.state)
    | .error (.err e) => .error (.err e)
    | .error (.panic _) => .error (.panic .v1)
  msgSerialize := Message.serialize
  msgDeserialize := fun ep rem =>
    match Message.deserialize spqrPolyApi ep rem with
    | .ok m => .ok m
    | .error e => .error (.err e)
  msgEpoch := Message.epoch
  initV1Inner := fun dir authKey =>
    match dir with
    | .a2b =>
      match States.init_a spqrPolyApi auth authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1
    | .b2a =>
      match States.init_b spqrPolyApi auth authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1

private theorem spqrDepsWithMac_eq_ofAuth (F : ShaCompress) (K : MlKem) (mac : HmacFn) :
    spqrDepsWithMac F K mac = spqrDepsOfAuth (spqrAuthApiWithMac F mac) K := by
  unfold spqrDepsWithMac spqrDepsOfAuth
  congr 1
  · funext st tape; rcases st.send K tape with (_ | _) | ⟨_, _⟩ <;> rfl
  · funext st msg; rcases st.recv K msg with (_ | _) | _ <;> rfl

private theorem spqrDeps_eq_ofAuth (F : ShaCompress) (K : MlKem) :
    spqrDeps F K = spqrDepsOfAuth (spqrAuthApi F) K := by
  unfold spqrDeps spqrDepsOfAuth
  congr 1
  · funext st tape; rcases st.send K tape with (_ | _) | ⟨_, _⟩ <;> rfl
  · funext st msg; rcases st.recv K msg with (_ | _) | _ <;> rfl

@[simp]
theorem spqrDepsWithMac_hmacFnOfSha (F : ShaCompress) (K : MlKem) :
    spqrDepsWithMac F K (hmacFnOfSha F) = spqrDeps F K := by
  rw [spqrDepsWithMac_eq_ofAuth, spqrDeps_eq_ofAuth, spqrAuthApiWithMac_hmacFnOfSha]

/-- Assembled SPQR V1 send model (`SpqrModel`) parameterized by `F`, `K`, and `mac : HmacFn`. -/
def spqrV1WithMac (F : ShaCompress) (K : MlKem) (mac : HmacFn := hmacFnOfSha F) : SpqrModel :=
  toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)

/-- Assembled SPQR V1 recv model (`SpqrRecvModel`) parameterized by `F`, `K`, and `mac : HmacFn`. -/
def spqrV1RecvWithMac (F : ShaCompress) (K : MlKem) (mac : HmacFn := hmacFnOfSha F) : SpqrRecvModel :=
  toSpqrRecvModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)

end Symbolic.Swarm.SHARED.HookAuth
