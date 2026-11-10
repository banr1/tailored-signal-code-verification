/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Specifications.Refinement.Concretization
public import Symbolic.Specifications.Refinement.ModelTraces
public import Symbolic.Proofs.SpecLemmas.ImageSymbolsProofDefs

/-!
# Concrete SPQR Symbol Semantics

Defines the concrete SPQR symbol semantics `spqrModelOf` and its byte-level send/receive
projections over an `ExternInterpretation`, together with `gamma` evaluation instances and
`spqrKeyBytes` lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.SpqrSemOf

open DY.Comparse
open DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (mlkem768FromSeedSymbol mlkem768ValidatePkSymbol mlkem768Encaps1Symbol mlkem768Encaps2Symbol mlkem768DecapsSymbol libcruxHmacSymbol)

abbrev SpqrSem : Type := OpaqueSymbolSemantics

/-! ## Authenticator and SPQR Model Wrappers -/

abbrev HmacFn : Type :=
  List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))

def hmacFnOfSha (F : ShaCompress) : HmacFn :=
  fun key data => some (hmacWith F key data)

def hmacFnOf (i : ExternInterpretation) : HmacFn :=
  fun key data => i libcruxHmacSymbol [key, data]

def bytesToVec (n : Nat) (bs : List (BitVec 8)) : List.Vector (BitVec 8) n :=
  ⟨(bs ++ List.replicate n 0#8).take n, by
    rw [List.length_take, List.length_append, List.length_replicate]
    omega⟩

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

def macCtWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    Except SpqrPanic Bytes :=
  let body := Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct
  if self.macKey.length < 2 ^ 32 ∧ body.length < 2 ^ 32 then
    match mac self.macKey body with
    | some tag =>
      if 32 ≤ tag.length then
        .ok (tag.take 32)
      else
        .error (.site "Authenticator::mac_ct: hmac tag shorter than 32 bytes")
    | none =>
      .error (.site "Authenticator::mac_ct: libcrux_hmac::hmac returned none")
  else
    .error hmacU32UnwrapPanic

@[scoped simp]
theorem macCtWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    macCtWithMac (hmacFnOfSha F) self ep ct = self.macCt F ep ct := by
  simp [macCtWithMac, Authenticator.macCt, Authenticator.macCtUnchecked,
    Authenticator.macSize, hmacFnOfSha, length_hmacWith]

def macHdrWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    Except SpqrPanic Bytes :=
  let body := Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr
  if self.macKey.length < 2 ^ 32 ∧ body.length < 2 ^ 32 then
    match mac self.macKey body with
    | some tag =>
      if 32 ≤ tag.length then
        .ok (tag.take 32)
      else
        .error (.site "Authenticator::mac_hdr: hmac tag shorter than 32 bytes")
    | none =>
      .error (.site "Authenticator::mac_hdr: libcrux_hmac::hmac returned none")
  else
    .error hmacU32UnwrapPanic

@[scoped simp]
theorem macHdrWithMac_hmacFnOfSha (F : ShaCompress)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    macHdrWithMac (hmacFnOfSha F) self ep hdr = self.macHdr F ep hdr := by
  simp [macHdrWithMac, Authenticator.macHdr, Authenticator.macHdrUnchecked,
    Authenticator.macSize, hmacFnOfSha, length_hmacWith]

def verifyCtErrorWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch)
    (ct expectedMac : Bytes) : Except SpqrPanic (Except Error Unit) := do
  let computed ← macCtWithMac mac self ep ct
  let diff ← CryptoVerification.LibsignalSpqrV1.compare expectedMac computed
  return if diff != 0#8 then .error .macVerifyFailed else .ok ()

@[scoped simp]
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

def verifyHdrErrorWithMac (mac : HmacFn) (self : Authenticator) (ep : Epoch)
    (hdr expectedMac : Bytes) : Except SpqrPanic (Except Error Unit) := do
  let computed ← macHdrWithMac mac self ep hdr
  let diff ← CryptoVerification.LibsignalSpqrV1.compare expectedMac computed
  return if diff != 0#8 then .error .macVerifyFailed else .ok ()

@[scoped simp]
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

@[scoped simp]
theorem spqrAuthApiWithMac_hmacFnOfSha (F : ShaCompress) :
    spqrAuthApiWithMac F (hmacFnOfSha F) = spqrAuthApi F := by
  unfold spqrAuthApiWithMac spqrAuthApi
  simp

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

@[scoped simp]
theorem spqrDepsWithMac_hmacFnOfSha (F : ShaCompress) (K : MlKem) :
    spqrDepsWithMac F K (hmacFnOfSha F) = spqrDeps F K := by
  rw [spqrDepsWithMac_eq_ofAuth, spqrDeps_eq_ofAuth, spqrAuthApiWithMac_hmacFnOfSha]

def spqrV1WithMac (F : ShaCompress) (K : MlKem) (mac : HmacFn := hmacFnOfSha F) : SpqrModel :=
  toSpqrModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)

@[scoped simp]
theorem spqrV1WithMac_hmacFnOfSha (F : ShaCompress) (K : MlKem) :
    spqrV1WithMac F K (hmacFnOfSha F) = spqrV1 F K := by
  unfold spqrV1WithMac spqrV1 spqrV1Assembled
  rw [spqrDepsWithMac_hmacFnOfSha]

def spqrV1RecvWithMac (F : ShaCompress) (K : MlKem) (mac : HmacFn := hmacFnOfSha F) : SpqrRecvModel :=
  toSpqrRecvModel (spqrDepsWithMac F K mac) (spqrHkdfWith F)

/-! ## Byte-Level Send and Receive Projections -/

def spqrSendB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Option (Bytes × Bytes × Bytes) :=
  match (spqrV1WithMac F K mac).send st coins with
  | some (st', salt?, msg) =>
      let keyBytes := match salt? with
        | some v => v.toList
        | none => []
      some (st', keyBytes, msg)
  | none => none

def spqrSendStateB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (st', _, _) => st'
  | none => []

def spqrSendKeyB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (_, key, _) => key
  | none => []

def spqrSendMsgB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st coins : Bytes) : Bytes :=
  match spqrSendB F K mac st coins with
  | some (_, _, msg) => msg
  | none => []

def spqrRecvB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Option (Bytes × Option Bytes) :=
  match (spqrV1RecvWithMac F K mac).recv st msg with
  | .ok (st', key?) => some (st', key?)
  | .error _ => none

def spqrRecvStateB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Bytes :=
  match spqrRecvB F K mac st msg with
  | some (st', _) => st'
  | none => []

def spqrRecvKeyB (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg : Bytes) : Bytes :=
  match spqrRecvB F K mac st msg with
  | some (_, some k) => k
  | _ => []

def spqrSendStateOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendStateB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrSendKeyOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendKeyB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrSendMsgOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrSendMsgB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrRecvStateOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrRecvStateB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

def spqrRecvKeyOf (i : ExternInterpretation) : Bytes → Bytes → Bytes :=
  spqrRecvKeyB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

/-! ## Interpretation-Parameterized SPQR Model -/

/-- SPQR model wrapping `i : ExternInterpretation`'s SHA-256, ML-KEM-768, and `libcrux_hmac` symbols. -/
def spqrModelOf (i : ExternInterpretation) : SpqrModel :=
  spqrV1WithMac (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i)

/-- Convert `Salt = Option (List.Vector (BitVec 8) 32)` to `HwBytes` (`[]` on `none`, `v.toList` on `some v`). -/
def saltToBytes (s : Salt) : HwBytes :=
  match s with
  | some v => v.toList
  | none => []

/-- 4-byte little-endian encoding of `1 : UInt32`, matching `gamma i S g (DY.Spqr.spqrIdx 1)`. -/
def spqrIdx1Bytes : HwBytes := [1#8, 0#8, 0#8, 0#8]

/-! ## Concretization Subfunction Instances -/

section GammaSpqr

variable (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)

unseal DY.Bytes in
instance subLit : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subRandom : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrInit : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendState : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendKey : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrSendMsg : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrRecvState : DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrRecvKey : DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subSpqrChainKey : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm32 (t : Nat) : gamma i S g (randTerm t 32) = g.σ t 32 := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g)]
  rfl

end GammaSpqr

/-! ## Key Padding and Send Projection Lemmas -/

@[scoped simp]
theorem spqrKeyBytes_nil : spqrKeyBytes [] = List.replicate 32 0#8 := by
  simp [spqrKeyBytes]

theorem spqrKeyBytes_of_length_32 {k : HwBytes} (hk : k.length = 32) :
    spqrKeyBytes k = k := by
  unfold spqrKeyBytes
  rw [← hk, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

@[scoped simp]
theorem spqrKeyBytes_saltToBytes (s : Salt) :
    spqrKeyBytes (saltToBytes s) =
      match s with
      | some v => v.toList
      | none => List.replicate 32 0#8 := by
  cases s with
  | none => exact spqrKeyBytes_nil
  | some v =>
    dsimp [saltToBytes]
    exact spqrKeyBytes_of_length_32 (List.Vector.toList_length v)

/-- When `(spqrModelOf i).send stBytes coinsBytes = some (st', salt?, msg)`, `spqrSendStateOf i`,
`spqrSendKeyOf i`, and `spqrSendMsgOf i` evaluate to `st'`, `saltToBytes salt?`, and `msg`. -/
theorem spqrSendOf_of_send_some (i : ExternInterpretation)
    {stBytes coinsBytes st' msg : HwBytes} {salt? : Salt}
    (hsend : (spqrModelOf i).send stBytes coinsBytes = some (st', salt?, msg)) :
    spqrSendStateOf i stBytes coinsBytes = st' ∧
    spqrSendKeyOf i stBytes coinsBytes = saltToBytes salt? ∧
    spqrSendMsgOf i stBytes coinsBytes = msg := by
  have hB : spqrSendB (sha256CompressFunction i) (mlkemOf i) (hmacFnOf i) stBytes coinsBytes =
      some (st', saltToBytes salt?, msg) := by
    unfold spqrSendB
    change (match (spqrModelOf i).send stBytes coinsBytes with
      | some (st', salt?, msg) => some (st', saltToBytes salt?, msg)
      | none => none) = some (st', saltToBytes salt?, msg)
    rw [hsend]
  unfold spqrSendStateOf spqrSendKeyOf spqrSendMsgOf
    spqrSendStateB spqrSendKeyB spqrSendMsgB
  rw [hB]
  exact ⟨rfl, rfl, rfl⟩

end Symbolic.Swarm.TRREF.SpqrSemOf
