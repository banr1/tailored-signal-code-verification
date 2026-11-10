/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure
public import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.SR.ModelW
public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
public import Symbolic.Proofs.Swarm.SHARED.HookAuthPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Specifications.Refinement.Statement
import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewSpqrSalt
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Fresh Pre-Key Recipient Session Decryption Inversion

Inverts an accepting `recvPrekeyState` step on Bob's freshly initialized V4 session, establishes
post-accept session record scope and serialization equations, and relates `SpqrSemOf.spqrModelOf`
to empty-key-as-`none` SPQR decryption.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

theorem coinsOf_eq_bytesToKey32 {d : HwBytes} (hd : d.length = 32) :
    RpkCli.pureCoinsOf d = HKDF.bytesToKey32 d := by
  unfold RpkCli.pureCoinsOf
  rw [List.take_append_of_le_length (Nat.le_of_eq hd.symm),
    List.take_of_length_le (Nat.le_of_eq hd)]

theorem rpkNew_record_facts_of_wfPq {W : PEParams} {st' : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st') (hsess : st'.session = some (x, g))
    (hppk : g.session.pendingPreKey = false) :
    TR.Pure.slots_RecordInScopeP ⟨some (pqSession x g)⟩ ∧
    TR.Pure.BinSessionInv (pqSession x g) ∧
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 ∧
    encodeRecordUnderExtras (fun _ => x) g =
      CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩ ∧
    encodeRecordUnderExtras (fun _ => x) g =
      recordBytes (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec (pqSession x g)) := by
  have hscopeP := recordInScopeP_of_wfPq hwf hsess
  have hlen31 := (reachPqInvPure_of_wfPq hwf hsess).2.2
  have hbin : TR.Pure.BinSessionInv (pqSession x g) := (recordCanonical_Q_of_wfPq hwf hsess).2.2
  exact ⟨hscopeP, hbin, hlen31,
    encodeRecordX_eq_encodeRecord_pqSession x g,
    encodeRecordX_eq_recordBytes_of_wfPq hwf hsess hppk⟩

/-- Unpacks an accepting `recvPrekeyState` call for `.B` into inner message decoding,
`SignalPqxdh.Model.acceptKeys`, and `SessionState.tryDecryptFromRecord`. -/
theorem recvPrekeyState_some_some_inv {X : UnreachedPqxdhPrimitives} {P : PEParams}
    {me : LocalIdentity} {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {rc : BitVec 256}
    {x : RecordExtras} {g : GhostState HwBytes} {pt : HwBytes}
    (h : recvPrekeyState X P .B me k m rc = some (some (x, g, pt))) :
    ∃ (inner : SignalMessage) (dk : SignalPqxdh.DRKey) (st' : SessionState HwBytes),
      SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner =
        .ok inner ∧
      m.spkId = k.spkId ∧
      m.kpkId = k.kpkId ∧
      SignalPqxdh.Model.acceptKeys (modelPrims X P) (acceptInput P me k m) = some dk ∧
      (let st0 : SessionState HwBytes :=
         initializeRecipientSession (pqxdhSpqrSession P)
           ⟨(keyPairOf P.C me.idPriv).publicKey⟩
           ⟨⟨m.idPub⟩⟩ (keyPairOf P.C k.spkPriv)
           (HKDF.bytesToKey32 (ofU8 dk.rootKey))
           (HKDF.bytesToKey32 (ofU8 dk.chainKey))
           (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
       SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
         ((pqxdhSessionParams P).expectedAddrs .B) inner .preKey rc st0 = (.ok pt, st')) ∧
      x = responderRecordExtras me m ∧
      g = ⟨.B, st', 1, [1]⟩ ∧
      ReachablePqxdhSession P me x g := by
  have hrpq : ReachablePqxdhSession P me x g := ReachablePqxdhSession.recvPrekey X .B me k m rc x g pt h
  unfold recvPrekeyState at h
  rcases htf : SignalMessage.tryFrom CryptoVerification.LibsignalProtoCodec.protoSignalCodec m.inner with
    _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    split_ifs at h with hids
    · simp at h
    · push Not at hids
      rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X P) (acceptInput P me k m) with
        _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        let st0 : SessionState HwBytes :=
          initializeRecipientSession (pqxdhSpqrSession P)
            ⟨(keyPairOf P.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf P.C k.spkPriv)
            (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey))
            (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        rcases hdec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
            ((pqxdhSessionParams P).expectedAddrs .B) inner .preKey rc st0 with ⟨e | pt', st'⟩
        · rw [hdec] at h; cases e <;> simp at h
        · rw [hdec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨inner, dk, st', rfl, hids.1, hids.2, rfl, hdec, rfl, rfl, hrpq⟩

private theorem mut_exec_bind_local {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.error e, s') => (.error e, s')
      | (.ok a, s') => Mut.exec (f a) s' := by
  unfold Mut.exec
  simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind,
    ExceptT.bindCont]
  cases m s with
  | mk res s' => cases res <;> rfl

private theorem mut_exec_get_local {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem mut_exec_throw_local {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem mut_exec_liftE_local {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

/-- Transfers an `.ok` run of `SessionState.tryDecryptWithStateW` from `spqrV1WithMac` to an
`Spqr` instance that maps non-32-byte raw keys to `none`. -/
theorem tryDecryptWithStateW_emptyAsNone_of_spqrV1WithMac_ok
    {C : Crypto} {W : Proofs.libsignal.SR.AesW}
    {F : ShaCompress} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {H : Symbolic.Swarm.SHARED.HookAuth.HmacFn}
    {S₀ S' : Spqr HwBytes HwBytes}
    {expected : Option HwBytes} {msg : SignalMessage} {msgType : MessageType}
    {coins : BitVec 256} {st0 st' : SessionState HwBytes} {pt : HwBytes}
    (hdec : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W
      S₀ expected msg msgType coins) st0 = (.ok pt, st'))
    (hpan_eq : S'.recvPanics = S₀.recvPanics)
    (hrecv0 : S₀.recv = (Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac F K H).recv)
    (hrecv_eq : S'.recv = (fun s m =>
      match (Symbolic.Swarm.SHARED.HookAuth.spqrV1RecvWithMac F K H).recv s m with
      | .ok (st', key?) =>
        .ok (st', match key? with
                  | some k => if hk : k.length = 32 then some ⟨k, hk⟩ else none
                  | none => none)
      | .error b => .error b)) :
    Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W
      S' expected msg msgType coins) st0 =
      (.ok pt, st') := by
  unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW at hdec ⊢
  rw [mut_exec_bind_local] at hdec ⊢
  generalize hf : Mut.exec TripleRatchet.fromSessionState st0 = f_res at hdec ⊢
  rcases f_res with ⟨e | sess0, s1⟩
  · cases hdec
  · dsimp only at hdec ⊢
    suffices htr :
        ∀ pt1 sess1,
          Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W
            S₀ expected msg msgType coins) sess0 = (.ok pt1, sess1) →
          Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W
            S' expected msg msgType coins) sess0 = (.ok pt1, sess1) by
      generalize hd : Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W
          S₀ expected msg msgType coins) sess0 = d_res at hdec
      rcases d_res with ⟨err | pt1, sess1⟩
      · dsimp only at hdec
        rw [mut_exec_bind_local, mut_exec_liftE_local] at hdec; cases hdec
      · rw [htr pt1 sess1 hd]; exact hdec
    intro pt1 sess1 hd
    unfold Proofs.libsignal.SR.TripleRatchet.decryptW at hd ⊢
    rw [mut_exec_bind_local] at hd ⊢
    generalize h1 : Mut.exec (TripleRatchet.onRatchet
        (RatchetState.ensureReceiverChain C msg.senderRatchetKey coins)) sess0 = r1_res at hd ⊢
    rcases r1_res with ⟨e1 | ck, s2⟩
    · cases hd
    · dsimp only at hd ⊢
      rw [mut_exec_bind_local] at hd ⊢
      generalize h2 : Mut.exec (TripleRatchet.onRatchet
          (RatchetState.consumeMessageKey C.F msg.senderRatchetKey ck msg.counter msgType)) s2 =
        r2_res at hd ⊢
      rcases r2_res with ⟨e2 | mkGen, s3⟩
      · cases hd
      · dsimp only at hd ⊢
        rw [mut_exec_bind_local, mut_exec_get_local] at hd ⊢
        dsimp only at hd ⊢
        rw [hpan_eq]
        generalize hp : S₀.recvPanics s3.pqrState msg.pqRatchet = pan_res at hd ⊢
        cases pan_res
        case true =>
          simp only [↓reduceIte] at hd
          rw [mut_exec_bind_local, mut_exec_throw_local] at hd; cases hd
        simp only [Bool.false_eq_true, ↓reduceIte] at hd ⊢
        generalize hsp : S₀.recv s3.pqrState msg.pqRatchet = sp_res at hd
        rcases sp_res with b | ⟨newPqrState, pqrKey⟩
        · cases b <;>
            { dsimp only at hd; rw [mut_exec_bind_local, mut_exec_throw_local] at hd; cases hd }
        · have hsp0 : (Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac F K H).recv
              s3.pqrState msg.pqRatchet = .ok (newPqrState, pqrKey) := by
            rw [← hrecv0]; exact hsp
          rw [spqrV1WithMacEmptyAsNone_recv_of_spqrV1WithMac_recv_ok (S' := S') hsp0 hrecv_eq]
          exact hd

private def spqrDepsOfAuthLocal (auth : CryptoVerification.LibsignalSpqrV1.AuthApi)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem) : CryptoVerification.LibsignalSpqrV1.SpqrApiDeps where
  V1StatePB := CryptoVerification.LibsignalSpqrV1.V1State
  decodeState := fun bs =>
    match CryptoVerification.LibsignalSpqrV1.Proto.decodeState bs with
    | .ok st => .ok (CryptoVerification.LibsignalSpqrV1.pqRatchetStateToPb st)
    | .error _ => .error ()
  encodeState := fun st =>
    CryptoVerification.LibsignalSpqrV1.Proto.encodeState
      (CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState st)
  States := CryptoVerification.LibsignalSpqrV1.States CryptoVerification.LibsignalSpqrV1.spqrPolyApi auth
  statesFromPb := fun pb =>
    CryptoVerification.LibsignalSpqrV1.liftStatesResult
      (CryptoVerification.LibsignalSpqrV1.States.from_pb CryptoVerification.LibsignalSpqrV1.spqrPolyApi auth pb)
  statesIntoPb := CryptoVerification.LibsignalSpqrV1.States.into_pb
  MessageV1 := CryptoVerification.LibsignalSpqrV1.Message CryptoVerification.LibsignalSpqrV1.spqrPolyApi
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
  msgSerialize := CryptoVerification.LibsignalSpqrV1.Message.serialize
  msgDeserialize := fun ep rem =>
    match CryptoVerification.LibsignalSpqrV1.Message.deserialize
        CryptoVerification.LibsignalSpqrV1.spqrPolyApi ep rem with
    | .ok m => .ok m
    | .error e => .error (.err e)
  msgEpoch := CryptoVerification.LibsignalSpqrV1.Message.epoch
  initV1Inner := fun dir authKey =>
    match dir with
    | .a2b =>
      match CryptoVerification.LibsignalSpqrV1.States.init_a
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi auth authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1
    | .b2a =>
      match CryptoVerification.LibsignalSpqrV1.States.init_b
          CryptoVerification.LibsignalSpqrV1.spqrPolyApi auth authKey with
      | .ok st => .ok st.into_pb
      | .error _ => .error .v1

theorem spqrModelOf_eq_hookAuth_of_ext {interp : ExternInterpretation}
    (hExt : ExternContractsHoldCli interp) :
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp =
      Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp)
        (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
  have hmct : Symbolic.Swarm.TRREF.SpqrSemOf.macCtWithMac (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      Symbolic.Swarm.SHARED.HookAuth.macCtWithMac (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
    funext self ep ct
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.macCtWithMac Symbolic.Swarm.SHARED.HookAuth.macCtWithMac
      Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf Symbolic.Swarm.SHARED.HookAuth.hmacFnOf
    dsimp only
    split_ifs
    · cases hm : interp DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol
          [self.macKey, CryptoVerification.LibsignalSpqrV1.Authenticator.ctLabel ++
            CryptoGames.HMAC.toBEBytes 8 ep ++ ct] with
      | none => rfl
      | some tag =>
        have ht : tag.length = 32 := hExt.1.hmac_tag_length _ _ _ hm
        simp [ht, List.take_of_length_le (Nat.le_of_eq ht)]
    · rfl
  have hmhdr : Symbolic.Swarm.TRREF.SpqrSemOf.macHdrWithMac (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      Symbolic.Swarm.SHARED.HookAuth.macHdrWithMac (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
    funext self ep hdr
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.macHdrWithMac Symbolic.Swarm.SHARED.HookAuth.macHdrWithMac
      Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf Symbolic.Swarm.SHARED.HookAuth.hmacFnOf
    dsimp only
    split_ifs
    · cases hm : interp DY.Libsignal.PQXDH.Refinement.libcruxHmacSymbol
          [self.macKey, CryptoVerification.LibsignalSpqrV1.Authenticator.hdrLabel ++
            CryptoGames.HMAC.toBEBytes 8 ep ++ hdr] with
      | none => rfl
      | some tag =>
        have ht : tag.length = 32 := hExt.1.hmac_tag_length _ _ _ hm
        simp [ht, List.take_of_length_le (Nat.le_of_eq ht)]
    · rfl
  have hvct : Symbolic.Swarm.TRREF.SpqrSemOf.verifyCtErrorWithMac (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      Symbolic.Swarm.SHARED.HookAuth.verifyCtErrorWithMac (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
    funext self ep ct expectedMac
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.verifyCtErrorWithMac Symbolic.Swarm.SHARED.HookAuth.verifyCtErrorWithMac
    rw [hmct]
  have hvhdr : Symbolic.Swarm.TRREF.SpqrSemOf.verifyHdrErrorWithMac (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      Symbolic.Swarm.SHARED.HookAuth.verifyHdrErrorWithMac (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
    funext self ep hdr expectedMac
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.verifyHdrErrorWithMac Symbolic.Swarm.SHARED.HookAuth.verifyHdrErrorWithMac
    rw [hmhdr]
  have hauth : Symbolic.Swarm.TRREF.SpqrSemOf.spqrAuthApiWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      Symbolic.Swarm.SHARED.HookAuth.spqrAuthApiWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) := by
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrAuthApiWithMac Symbolic.Swarm.SHARED.HookAuth.spqrAuthApiWithMac
    rw [hmhdr, hmct, hvhdr, hvct]
  have hd1 : Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf interp) (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp) =
      spqrDepsOfAuthLocal (Symbolic.Swarm.TRREF.SpqrSemOf.spqrAuthApiWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf interp)) (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf interp) := by
    unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac spqrDepsOfAuthLocal
    congr 1
    · funext st tape; rcases st.send _ tape with (_ | _) | ⟨_, _⟩ <;> rfl
    · funext st msg; rcases st.recv _ msg with (_ | _) | _ <;> rfl
  have hd2 : Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp) (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) =
      spqrDepsOfAuthLocal (Symbolic.Swarm.SHARED.HookAuth.spqrAuthApiWithMac (sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp)) (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp) := by
    unfold Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac spqrDepsOfAuthLocal
    congr 1
    · funext st tape; rcases st.send _ tape with (_ | _) | ⟨_, _⟩ <;> rfl
    · funext st msg; rcases st.recv _ msg with (_ | _) | _ <;> rfl
  have hK : Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf interp = Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp := rfl
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1WithMac
    Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac
  rw [hd1, hd2, hauth, hK]

end Symbolic.Swarm.CREF.Cli.Slots
