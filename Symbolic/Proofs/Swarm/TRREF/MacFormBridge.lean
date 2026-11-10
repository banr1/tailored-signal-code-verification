/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs

/-!
# SPQR HMAC Form Bridge

Shows that under the 32-byte HMAC tag-length hypothesis
`hlen : ∀ k d t, mac k d = some t → t.length = 32`, the truncated-tag SPQR definitions in
`SpqrSemOf` agree with the raw-tag definitions in `HookAuth` and `SpqrBytes`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.MacFormBridge

open CryptoGames.HMAC (toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (sha256CompressFunction)
open Symbolic.Swarm.SHARED

/-! ## Authenticator MAC Operations -/

theorem macHdrWithMac_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (self : Authenticator) (ep : Epoch) (hdr : Bytes) :
    SpqrSemOf.macHdrWithMac mac self ep hdr =
      HookAuth.macHdrWithMac mac self ep hdr := by
  unfold SpqrSemOf.macHdrWithMac HookAuth.macHdrWithMac
  dsimp only
  split
  · rcases hmac : mac self.macKey (Authenticator.hdrLabel ++ toBEBytes 8 ep ++ hdr) with _ | tag
    · rfl
    · have htag : tag.length = 32 := hlen _ _ _ hmac
      simp [htag]
  · rfl

theorem macHdrWithMac_fun_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.macHdrWithMac mac = HookAuth.macHdrWithMac mac := by
  funext self ep hdr
  exact macHdrWithMac_spqrSemOf_eq_hookAuth hlen self ep hdr

theorem macCtWithMac_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (self : Authenticator) (ep : Epoch) (ct : Bytes) :
    SpqrSemOf.macCtWithMac mac self ep ct =
      HookAuth.macCtWithMac mac self ep ct := by
  unfold SpqrSemOf.macCtWithMac HookAuth.macCtWithMac
  dsimp only
  split
  · rcases hmac : mac self.macKey (Authenticator.ctLabel ++ toBEBytes 8 ep ++ ct) with _ | tag
    · rfl
    · have htag : tag.length = 32 := hlen _ _ _ hmac
      simp [htag]
  · rfl

theorem macCtWithMac_fun_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.macCtWithMac mac = HookAuth.macCtWithMac mac := by
  funext self ep ct
  exact macCtWithMac_spqrSemOf_eq_hookAuth hlen self ep ct

theorem verifyHdrErrorWithMac_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (self : Authenticator) (ep : Epoch) (hdr expectedMac : Bytes) :
    SpqrSemOf.verifyHdrErrorWithMac mac self ep hdr expectedMac =
      HookAuth.verifyHdrErrorWithMac mac self ep hdr expectedMac := by
  unfold SpqrSemOf.verifyHdrErrorWithMac HookAuth.verifyHdrErrorWithMac
  rw [macHdrWithMac_spqrSemOf_eq_hookAuth hlen]

theorem verifyHdrErrorWithMac_fun_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.verifyHdrErrorWithMac mac = HookAuth.verifyHdrErrorWithMac mac := by
  funext self ep hdr expectedMac
  exact verifyHdrErrorWithMac_spqrSemOf_eq_hookAuth hlen self ep hdr expectedMac

theorem verifyCtErrorWithMac_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (self : Authenticator) (ep : Epoch) (ct expectedMac : Bytes) :
    SpqrSemOf.verifyCtErrorWithMac mac self ep ct expectedMac =
      HookAuth.verifyCtErrorWithMac mac self ep ct expectedMac := by
  unfold SpqrSemOf.verifyCtErrorWithMac HookAuth.verifyCtErrorWithMac
  rw [macCtWithMac_spqrSemOf_eq_hookAuth hlen]

theorem verifyCtErrorWithMac_fun_spqrSemOf_eq_hookAuth {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.verifyCtErrorWithMac mac = HookAuth.verifyCtErrorWithMac mac := by
  funext self ep ct expectedMac
  exact verifyCtErrorWithMac_spqrSemOf_eq_hookAuth hlen self ep ct expectedMac

/-! ## SPQR Model Instantiations -/

theorem spqrAuthApiWithMac_spqrSemOf_eq_hookAuth (F : ShaCompress) {mac : HookAuth.HmacFn}
    (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.spqrAuthApiWithMac F mac = HookAuth.spqrAuthApiWithMac F mac := by
  unfold SpqrSemOf.spqrAuthApiWithMac HookAuth.spqrAuthApiWithMac
  rw [macHdrWithMac_fun_spqrSemOf_eq_hookAuth hlen,
    macCtWithMac_fun_spqrSemOf_eq_hookAuth hlen,
    verifyHdrErrorWithMac_fun_spqrSemOf_eq_hookAuth hlen,
    verifyCtErrorWithMac_fun_spqrSemOf_eq_hookAuth hlen]

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

private theorem spqrDepsWithMac_spqrSemOf_eq_ofAuth (F : ShaCompress) (K : MlKem)
    (mac : HookAuth.HmacFn) :
    SpqrSemOf.spqrDepsWithMac F K mac =
      spqrDepsOfAuth (SpqrSemOf.spqrAuthApiWithMac F mac) K := by
  unfold SpqrSemOf.spqrDepsWithMac spqrDepsOfAuth
  congr 1
  · funext st tape; rcases st.send K tape with (_ | _) | ⟨_, _⟩ <;> rfl
  · funext st msg; rcases st.recv K msg with (_ | _) | _ <;> rfl

private theorem spqrDepsWithMac_hookAuth_eq_ofAuth (F : ShaCompress) (K : MlKem)
    (mac : HookAuth.HmacFn) :
    HookAuth.spqrDepsWithMac F K mac =
      spqrDepsOfAuth (HookAuth.spqrAuthApiWithMac F mac) K := by
  unfold HookAuth.spqrDepsWithMac spqrDepsOfAuth
  congr 1
  · funext st tape; rcases st.send K tape with (_ | _) | ⟨_, _⟩ <;> rfl
  · funext st msg; rcases st.recv K msg with (_ | _) | _ <;> rfl

theorem spqrDepsWithMac_spqrSemOf_eq_hookAuth (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.spqrDepsWithMac F K mac = HookAuth.spqrDepsWithMac F K mac := by
  rw [spqrDepsWithMac_spqrSemOf_eq_ofAuth, spqrDepsWithMac_hookAuth_eq_ofAuth,
    spqrAuthApiWithMac_spqrSemOf_eq_hookAuth F hlen]

theorem spqrV1WithMac_spqrSemOf_eq_hookAuth (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.spqrV1WithMac F K mac = HookAuth.spqrV1WithMac F K mac := by
  unfold SpqrSemOf.spqrV1WithMac HookAuth.spqrV1WithMac
  rw [spqrDepsWithMac_spqrSemOf_eq_hookAuth F K hlen]

theorem spqrV1RecvWithMac_spqrSemOf_eq_hookAuth (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32) :
    SpqrSemOf.spqrV1RecvWithMac F K mac = HookAuth.spqrV1RecvWithMac F K mac := by
  unfold SpqrSemOf.spqrV1RecvWithMac HookAuth.spqrV1RecvWithMac
  rw [spqrDepsWithMac_spqrSemOf_eq_hookAuth F K hlen]

/-! ## Byte-Level Send and Receive Projections -/

theorem spqrSendB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st coins : Bytes) :
    SpqrSemOf.spqrSendB F K mac st coins = SpqrBytes.spqrSendB F K mac st coins := by
  unfold SpqrSemOf.spqrSendB SpqrBytes.spqrSendB
  rw [spqrV1WithMac_spqrSemOf_eq_hookAuth F K hlen]
  rcases (HookAuth.spqrV1WithMac F K mac).send st coins with _ | ⟨_, _ | _, _⟩ <;> rfl

theorem spqrSendStateB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st coins : Bytes) :
    SpqrSemOf.spqrSendStateB F K mac st coins = SpqrBytes.spqrSendStateB F K mac st coins := by
  unfold SpqrSemOf.spqrSendStateB SpqrBytes.spqrSendStateB
  rw [spqrSendB_spqrSemOf_eq_spqrBytes F K hlen]
  rcases SpqrBytes.spqrSendB F K mac st coins with _ | ⟨_, _, _⟩ <;> rfl

theorem spqrSendKeyB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st coins : Bytes) :
    SpqrSemOf.spqrSendKeyB F K mac st coins = SpqrBytes.spqrSendKeyB F K mac st coins := by
  unfold SpqrSemOf.spqrSendKeyB SpqrBytes.spqrSendKeyB
  rw [spqrSendB_spqrSemOf_eq_spqrBytes F K hlen]
  rcases SpqrBytes.spqrSendB F K mac st coins with _ | ⟨_, _, _⟩ <;> rfl

theorem spqrSendMsgB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st coins : Bytes) :
    SpqrSemOf.spqrSendMsgB F K mac st coins = SpqrBytes.spqrSendMsgB F K mac st coins := by
  unfold SpqrSemOf.spqrSendMsgB SpqrBytes.spqrSendMsgB
  rw [spqrSendB_spqrSemOf_eq_spqrBytes F K hlen]
  rcases SpqrBytes.spqrSendB F K mac st coins with _ | ⟨_, _, _⟩ <;> rfl

theorem spqrRecvB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st msg : Bytes) :
    SpqrSemOf.spqrRecvB F K mac st msg = SpqrBytes.spqrRecvB F K mac st msg := by
  unfold SpqrSemOf.spqrRecvB SpqrBytes.spqrRecvB
  rw [spqrV1RecvWithMac_spqrSemOf_eq_hookAuth F K hlen]
  rcases (HookAuth.spqrV1RecvWithMac F K mac).recv st msg with _ | ⟨_, _⟩ <;> rfl

theorem spqrRecvStateB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st msg : Bytes) :
    SpqrSemOf.spqrRecvStateB F K mac st msg = SpqrBytes.spqrRecvStateB F K mac st msg := by
  unfold SpqrSemOf.spqrRecvStateB SpqrBytes.spqrRecvStateB
  rw [spqrRecvB_spqrSemOf_eq_spqrBytes F K hlen]
  rcases SpqrBytes.spqrRecvB F K mac st msg with _ | ⟨_, _⟩ <;> rfl

theorem spqrRecvKeyB_spqrSemOf_eq_spqrBytes (F : ShaCompress) (K : MlKem)
    {mac : HookAuth.HmacFn} (hlen : ∀ k d t, mac k d = some t → t.length = 32)
    (st msg : Bytes) :
    SpqrSemOf.spqrRecvKeyB F K mac st msg = SpqrBytes.spqrRecvKeyB F K mac st msg := by
  unfold SpqrSemOf.spqrRecvKeyB SpqrBytes.spqrRecvKeyB
  rw [spqrRecvB_spqrSemOf_eq_spqrBytes F K hlen]
  rcases SpqrBytes.spqrRecvB F K mac st msg with _ | ⟨_, _ | _⟩ <;> rfl

theorem spqrSendStateOf_spqrSemOf_eq_spqrBytes (i : ExternInterpretation)
    (hlen : ∀ k d t, HookAuth.hmacFnOf i k d = some t → t.length = 32) (st coins : Bytes) :
    SpqrSemOf.spqrSendStateOf i st coins =
      SpqrBytes.spqrSendStateB (sha256CompressFunction i) (HookAuth.mlkemOf i) (HookAuth.hmacFnOf i) st coins :=
  spqrSendStateB_spqrSemOf_eq_spqrBytes (sha256CompressFunction i) (HookAuth.mlkemOf i) hlen st coins

theorem spqrSendKeyOf_spqrSemOf_eq_spqrBytes (i : ExternInterpretation)
    (hlen : ∀ k d t, HookAuth.hmacFnOf i k d = some t → t.length = 32) (st coins : Bytes) :
    SpqrSemOf.spqrSendKeyOf i st coins =
      SpqrBytes.spqrSendKeyB (sha256CompressFunction i) (HookAuth.mlkemOf i) (HookAuth.hmacFnOf i) st coins :=
  spqrSendKeyB_spqrSemOf_eq_spqrBytes (sha256CompressFunction i) (HookAuth.mlkemOf i) hlen st coins

theorem spqrSendMsgOf_spqrSemOf_eq_spqrBytes (i : ExternInterpretation)
    (hlen : ∀ k d t, HookAuth.hmacFnOf i k d = some t → t.length = 32) (st coins : Bytes) :
    SpqrSemOf.spqrSendMsgOf i st coins =
      SpqrBytes.spqrSendMsgB (sha256CompressFunction i) (HookAuth.mlkemOf i) (HookAuth.hmacFnOf i) st coins :=
  spqrSendMsgB_spqrSemOf_eq_spqrBytes (sha256CompressFunction i) (HookAuth.mlkemOf i) hlen st coins

theorem spqrRecvStateOf_spqrSemOf_eq_spqrBytes (i : ExternInterpretation)
    (hlen : ∀ k d t, HookAuth.hmacFnOf i k d = some t → t.length = 32) (st msg : Bytes) :
    SpqrSemOf.spqrRecvStateOf i st msg =
      SpqrBytes.spqrRecvStateB (sha256CompressFunction i) (HookAuth.mlkemOf i) (HookAuth.hmacFnOf i) st msg :=
  spqrRecvStateB_spqrSemOf_eq_spqrBytes (sha256CompressFunction i) (HookAuth.mlkemOf i) hlen st msg

theorem spqrRecvKeyOf_spqrSemOf_eq_spqrBytes (i : ExternInterpretation)
    (hlen : ∀ k d t, HookAuth.hmacFnOf i k d = some t → t.length = 32) (st msg : Bytes) :
    SpqrSemOf.spqrRecvKeyOf i st msg =
      SpqrBytes.spqrRecvKeyB (sha256CompressFunction i) (HookAuth.mlkemOf i) (HookAuth.hmacFnOf i) st msg :=
  spqrRecvKeyB_spqrSemOf_eq_spqrBytes (sha256CompressFunction i) (HookAuth.mlkemOf i) hlen st msg

end Symbolic.Swarm.TRREF.MacFormBridge
