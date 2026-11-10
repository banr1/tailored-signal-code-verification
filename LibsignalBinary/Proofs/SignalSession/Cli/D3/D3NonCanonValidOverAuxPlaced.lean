/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonStage2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidMatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Non-Canonical Pre-Key Overwrite Model & Branch Agreement Helpers

Defines the overwrite `decrypt_prekey` model `decPkOverDef` and `Prev1` session-store
directory invariants (`cliOverSessInv`, `cliOverSessStoreAt`), bounds `spqrV1Init` and
`encodeRecordPrev1` serialized lengths, and proves Path-C Over branch agreement for
arbitrary `pm.serialized`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll

/-! ## 1. 32-Bit Serialized Length Bound for `spqrV1Init` -/

theorem spqrV1Init_length_le_2048 (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    (CryptoVerification.LibsignalSpqrV1.spqrV1Init F K dir k).length ≤ 2048 := by
  unfold CryptoVerification.LibsignalSpqrV1.spqrV1Init
    CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [CryptoVerification.LibsignalSpqrV1.initialState,
      CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams] at hst
    rcases hi : CryptoVerification.LibsignalSpqrV1.initInner
        (CryptoVerification.LibsignalSpqrV1.spqrDeps F K)
        CryptoVerification.LibsignalSpqrV1.Version.v1
        (CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection dir)
        (CryptoGames.HMAC.keyToBytes32 k) with p | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst
      subst hst'
      have hin := CryptoVerification.SpqrV1.Top.StateSize.initInner_spqrDeps_raw_le hi
      have hk : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
        simp [CryptoGames.HMAC.keyToBytes32]
      refine Nat.le_trans
        (CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState _) ?_
      simp only [CryptoVerification.SpqrV1.Top.StateSize.rawPqState,
        CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_none,
        CryptoVerification.SpqrV1.Top.StateSize.rawVN, hk]
      omega
  · decide

/-! ## 2. CLI `Prev1` Session-Store Directory Predicate -/

/-- Pure directory invariant required across `SessionFiles::store_session` on a `Prev1` record. -/
def cliOverSessInv (peer : AddrGhost) (d : DirGhost) : Prop :=
  peer.name.bytes.length < 2 ^ 32 ∧
  d.changed.length < 2 ^ 32 ∧
  (d.changed.length + 1 < 2 ^ 32 ∨ addressText peer.val ∈ d.changed.map Prod.fst)

def cliOverSessStoreAt (A : RustAlloc) (peer : AddrGhost) (self : BitVec 64)
    (d : DirGhost) : SepProp :=
  ⌜cliOverSessInv peer d⌝ ∗ dirAt A self d

theorem cliOverSessStoreAt_entails_dirAt (A : RustAlloc) (peer : AddrGhost)
    (self : BitVec 64) (d : DirGhost) :
    cliOverSessStoreAt A peer self d ⊢ dirAt A self d := by
  dsimp only [cliOverSessStoreAt]
  exact Entails.pure_left fun _ => Entails.refl _

/-! ## 3. Pure Overwrite `decrypt_prekey` Model (`decPkOverDef`) & Branch Agreement -/

theorem pkStoreKeys_ids_eq {F : FsFiles} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    (hk : pkStoreKeys F m = some k) :
    k.spkId = m.spkId ∧ k.kpkId = m.kpkId := by
  unfold pkStoreKeys at hk
  dsimp only at hk
  split at hk
  · split at hk
    · rw [Option.map_eq_some_iff] at hk
      obtain ⟨_, _, rfl⟩ := hk
      exact ⟨rfl, rfl⟩
    · cases hk
  · cases hk

theorem recvPrekeyState_of_accept_none (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (i : SignalMessage) (rc : BitVec 256)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hids : k.spkId = m.spkId ∧ k.kpkId = m.kpkId)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) = none) :
    recvPrekeyState X W P me k m rc = some none := by
  unfold recvPrekeyState
  rw [hi]
  dsimp only
  have hnot : ¬ (m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId) := by
    rintro (h1 | h2)
    · exact h1 hids.1.symm
    · exact h2 hids.2.symm
  rw [ite_eq_right hnot, hacc]

/-- Pure `RunSem.decryptPrekey` model covering empty, matching, and non-matching (`Prev1` archive)
sessions on `PreKeySignalMessage` inputs with arbitrary `pm.serialized`. -/
noncomputable def decPkOverDef (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8)) : SlotAns (List (BitVec 8)) :=
  let g := StoresGhost.opened
  let P := initParty peer
  match Slots.loadRec Scope F peer with
  | .error _ => some none
  | .ok r =>
    match g.identity.trusted cliIo.rd F peer pm.identityKey with
    | .error _ => some none
    | .ok false => some none
    | .ok true =>
      let saved := g.identity.saveUpd cliIo.rd F peer pm.identityKey
      match r.bind (·.currentSession) with
      | some s =>
        if SessMatchesPm s pm then
          decPkDef X W Scope F peer me pm coins
        else
          match pkToE? pm with
          | none => some none
          | some m =>
            match pkStoreKeys F m, g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
            | some k, .ok kp, .ok reg =>
              match recvPrekeyState X W P ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
              | none => none
              | some none => some none
              | some (some (_x, gs, pt)) =>
                match g.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
                | (.error _, _) => some none
                | (.ok (), kyber') =>
                  let oneTime' := match pm.preKeyId with
                    | none => g.oneTime
                    | some j => (removePreKey cliIo.rd F g.oneTime j).2
                  let ses' : Session (List (BitVec 8)) :=
                    { state := gs.session
                      pendingPreKey := none
                      pendingKyberPreKey := none
                      localRegistrationId := reg
                      remoteRegistrationId := m.regId
                      aliceBaseKey := djbKey m.baseKey }
                  let enc := E2E.Record.encSession (Over.clearPending s)
                  some (some ({ g with
                    identity := saved
                    kyber := kyber'
                    oneTime := oneTime'
                    sessions := g.sessions.put (addressText peer)
                      (Over.encodeRecordPrev1 ses' enc) }, pt))
            | _, _, _ => some none
      | none =>
        decPkDef X W Scope F peer me pm coins

theorem decPkOverDef_pathCOver_stage2_rej_placed {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hrej : StageP2PathCOverModelRejD3Placed X W F pm) :
    decPkOverDef X ⟨W.C, W.Q⟩ Scope F peer me pm coins = some none := by
  obtain ⟨m, i, hpk, hi, _hmsg_i, hcases⟩ := hrej
  unfold decPkOverDef
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [hcur]
  dsimp only
  rw [ite_eq_right hnot, hpk]
  dsimp only
  rcases hcases with (hsk | hkp | hreg) | ⟨k, kp, hsk, hkp, hacc⟩
  · rw [hsk]
  · cases pkStoreKeys F m with
    | none => rfl
    | some _ => rw [hkp]
  · cases pkStoreKeys F m with
    | none => rfl
    | some _ =>
      cases StoresGhost.opened.identity.keyPair cliIo.rd F with
      | error _ => rfl
      | ok _ => rw [hreg]
  · rw [hsk, hkp]
    cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
    | error _ => rfl
    | ok reg =>
      dsimp only
      rw [recvPrekeyState_of_accept_none X ⟨W.C, W.Q⟩ (initParty peer)
        ⟨kp.privateKey.bytes, reg⟩ k m i (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hsk)
        (hacc reg)]

/-! ## 4. 32-Bit `encodeRecordPrev1` Length Bound (`encodeRecordPrev1_pathCOver_lt_32`) -/

theorem encSession_clearPending_lt {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))}
    (hIn : Slots.scopeIn r) (hcur : r.currentSession = some s) :
    (E2E.Record.encSession (Over.clearPending s)).length < 2 ^ 21 + 2 ^ 31 + 20 := by
  rcases r with ⟨curOpt⟩
  dsimp only at hcur; subst hcur
  rcases hIn with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  have hb_strip : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq (Over.clearPending s))⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq (Over.clearPending s), rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hin0 := hin s rfl
      exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [Over.clearPending, Slots.PqValid.stripPq] at hk⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
      exact ⟨hr1, hr2, rfl, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [Over.clearPending, Slots.PqValid.stripPq] at hp,
        fun k hk => by simp [Over.clearPending, Slots.PqValid.stripPq] at hk, hss.2.2.2⟩
  have h21 : (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq (Over.clearPending s))⟩).length <
      2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge : (E2E.Record.encSession (Slots.PqValid.stripPq (Over.clearPending s))).length ≤
      (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq (Over.clearPending s))⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1 _
  have heq : (E2E.Record.encSession (Over.clearPending s)).length =
      (E2E.Record.encSession (Slots.PqValid.stripPq (Over.clearPending s))).length +
        (E2E.Record.bytesField 15 (Over.clearPending s).state.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq,
      show (E2E.Record.bytesField 15 []).length = 0 from rfl, List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15 (Over.clearPending s).state.pqRatchetState).length ≤
        (Over.clearPending s).state.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 (Over.clearPending s).state.pqRatchetState
  have hpq31 : (Over.clearPending s).state.pqRatchetState.length < 2 ^ 31 :=
    (hpq s rfl).2
  omega

set_option maxHeartbeats 400000 in
theorem encodeRecord_pathA_lt_22 {W : PEParams} {P : Party} {meE : LocalIdentity}
    {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {dk : SignalPqxdh.DRKey}
    {msg : SignalMessage} {rc : BitVec 256}
    {pt : List (BitVec 8)} {st' : SessionState (List (BitVec 8))}
    (htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs P) msg .preKey rc (pathAInitState W meE k m dk) =
      (.ok pt, st')) :
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 22 := by
  intro ses'
  let ses0 := pathAInitSession W meE k m dk
  have hIn0 := (pathAInitSession_scopeIn W meE k m dk).1
  rcases hIn0 with ⟨⟨hInP, hPqIn, hRep⟩, s0_, hCur0, hSessSc⟩
  injection hCur0 with hs0_eq; subst hs0_eq
  obtain ⟨hSeeds, _, _⟩ := hInP ses0 rfl
  obtain ⟨hRep1, hRep2, _, _⟩ := hRep ses0 rfl
  obtain ⟨hRC, _, _, hAbk⟩ := hSessSc
  have hTryV1 : SessionState.tryDecryptFromRecord W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs P) msg .preKey rc ses0.state = (.ok pt, st') := htry
  obtain ⟨hSeeds', hRC', _, _, key, hRecv⟩ :=
    CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs P) msg .preKey rc ses0.state st' pt hSeeds hRC hTryV1
  have hRep' := CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen W.C
    (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
    ((pqxdhSessionParams W).expectedAddrs P) msg .preKey rc ses0.state st' pt ⟨hRep1, hRep2⟩ hTryV1
  have hInitLe : ses0.state.pqRatchetState.length ≤ 2048 :=
    spqrV1Init_length_le_2048 W.C.F W.Q.K .b2a (HKDF.bytesToKey32 (E2E.ofU8 dk.pqrKey))
  have hPqSt' : st'.pqRatchetState.length ≤ ses0.state.pqRatchetState.length + 1128000 :=
    (CryptoVerification.SpqrV1.Top.StateSize.spqrV1_recv_validState_length_le W.C.F W.Q.K
      ses0.state.pqRatchetState msg.pqRatchet st'.pqRatchetState key
      (hPqIn ses0 rfl).1 (by omega) hRecv).2
  have hb_strip : E2E.RecordX.DeserializeScopeBounded ⟨some (Slots.PqValid.stripPq ses')⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq ses', rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      exact ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide),
        fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hPendFalse := (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs P) msg .preKey rc htry).1
      refine ⟨hRep'.1, hRep'.2, hPendFalse, ?_⟩
      change ses0.aliceBaseKey.length < _
      rcases hAbk with ha | ha <;> rw [ha] <;> decide
    · exact ⟨hRC', fun p hp => by simp [ses', Slots.PqValid.stripPq] at hp,
        fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1, hAbk⟩
  have h21 : (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length < 2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge : (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length ≤
      (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1 _
  have hle : (E2E.Record.encodeRecord ⟨some ses'⟩).length ≤
      (E2E.Record.encSession ses').length + 20 := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_le' 1 _
  have heq : (E2E.Record.encSession ses').length =
      (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length +
        (E2E.Record.bytesField 15 st'.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq, ses',
      show (E2E.Record.bytesField 15 []).length = 0 from rfl, List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15 st'.pqRatchetState).length ≤ st'.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 st'.pqRatchetState
  omega

theorem encodeRecordPrev1_pathCOver_lt_32 {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    (hd0 : DecPkOk₀ W Scope F peer.val me.val (pmOfE m pm.message))
    (hIn : Slots.scopeIn r) (hcur : r.currentSession = some s)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let enc := E2E.Record.encSession (Over.clearPending s)
    (Over.encodeRecordPrev1 ses' enc).length < 2 ^ 32 := by
  intro meE st' ses' enc
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  have htry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) (pathAInitState W meE k m dk) = (.ok pt, st') := by
    have ht := tryDecryptFromRecord_preKey_ver_eq (coins := coins)
      (st := pathAInitState W meE k m dk) hd0 (hmsg ▸ hver)
    rw [hmsg] at ht
    rw [ht]
    dsimp only [st']
    rcases hm : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk) with ⟨res, st1⟩
    rw [show ({ idPriv := kp.privateKey.bytes, regId := reg } : LocalIdentity) = meE from rfl, hm] at hok
    dsimp only at hok ⊢
    subst hok
    rfl
  have h22 : (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 22 :=
    encodeRecord_pathA_lt_22 htry
  have henc : enc.length < 2 ^ 21 + 2 ^ 31 + 20 := encSession_clearPending_lt hIn hcur
  have hlen2 : (E2E.Record.lenField 2 enc).length ≤ enc.length + 20 :=
    E2E.RecordX.lenField_length_le' 2 enc
  unfold Over.encodeRecordPrev1
  rw [List.length_append]
  omega

/-! ## 5. Path C Over Pure Branch Agreement (`decPkOverDef_pathCOver_*`) -/

theorem decPkOverDef_pathCOver_ver_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version ≠
      pm.message.messageVersion.zeroExtend 32) :
    decPkOverDef X W Scope F peer me pm coins = some none := by
  subst hmsg_i
  unfold decPkOverDef
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [hcur]
  dsimp only
  rw [ite_eq_right hnot, hpk]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m pm.message
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc,
    tryDecryptFromRecord_preKey_ver_ne hver]

theorem decPkOverDef_pathCOver_panic (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey}
    (hd0 : DecPkOk₀ W (fun _ => False) F peer.val me.val (pmOfE m pm.message))
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hpan : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error .panic) :
    decPkOverDef X W Scope F peer.val me.val pm coins = none := by
  subst hmsg_i
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  unfold decPkOverDef
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [hcur]
  dsimp only
  rw [ite_eq_right hnot, hpk]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m
    pm.message (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  have ht := tryDecryptFromRecord_preKey_ver_eq (coins := coins)
    (st := pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) hd0 (hmsg ▸ hver)
  rw [hmsg] at ht
  rw [ht]
  rcases hm : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at hpan
  dsimp only at hpan
  subst hpan
  rfl

theorem decPkOverDef_pathCOver_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {e : SignalProtocolError}
    (hd0 : DecPkOk₀ W (fun _ => False) F peer.val me.val (pmOfE m pm.message))
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (herr : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .error e)
    (hne : e ≠ .panic) :
    decPkOverDef X W Scope F peer.val me.val pm coins = some none := by
  subst hmsg_i
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  unfold decPkOverDef
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [hcur]
  dsimp only
  rw [ite_eq_right hnot, hpk]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m
    pm.message (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  have ht := tryDecryptFromRecord_preKey_ver_eq (coins := coins)
    (st := pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) hd0 (hmsg ▸ hver)
  rw [hmsg] at ht
  rw [ht]
  rcases hm : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) with ⟨res, st'⟩
  rw [hm] at herr
  dsimp only at herr
  subst herr
  dsimp only
  have hne' : SessionState.recordError .preKey e ≠ .panic :=
    mt (recordError_eq_panic_iff .preKey e).mp hne
  cases hr : SessionState.recordError .preKey e <;> first | exact absurd hr hne' | rfl

theorem decPkOverDef_pathCOver_mark_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))}
    (hd0 : DecPkOk₀ W (fun _ => False) F peer.val me.val (pmOfE m pm.message))
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).1 =
      .error ()) :
    decPkOverDef X W Scope F peer.val me.val pm coins = some none := by
  subst hmsg_i
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  unfold decPkOverDef
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [hcur]
  dsimp only
  rw [ite_eq_right hnot, hpk]
  dsimp only
  rw [hk, hkp, hreg]
  dsimp only
  rw [recvPrekeyState_of_accept_some X W (initParty peer.val) ⟨kp.privateKey.bytes, reg⟩ k m
    pm.message (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
  have ht := tryDecryptFromRecord_preKey_ver_eq (coins := coins)
    (st := pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) hd0 (hmsg ▸ hver)
  rw [hmsg] at ht
  rw [ht, hok]
  dsimp only
  rcases hmk : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
    ⟨r_mk, kyber'⟩
  rw [hmk] at hmark
  dsimp only at hmark
  subst hmark
  rfl

theorem decPkOverDef_pathCOver_ok (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))} {s : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {i : SignalMessage}
    {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {st' : SessionState (List (BitVec 8))} {kyber' : KyberGhost}
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd0 : DecPkOk₀ W (fun _ => False) F peer.val me.val (pmOfE m pm.message))
    (hIn : Slots.scopeIn r)
    (hload : Slots.loadRec Scope F peer.val = .ok (some r))
    (hcur : r.currentSession = some s)
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm)
    (hpk : pkToE? pm = some m) (hmsg_i : pm.message = i)
    (hi : SignalMessage.tryFrom protoSignalCodec m.inner = .ok i)
    (hk : pkStoreKeys F m = some k)
    (hkp : StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hreg : StoresGhost.opened.identity.regId cliIo.rd F = .ok reg)
    (hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W)
      (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m) = some dk)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) = (.ok pt, st'))
    (hmark : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey =
      (.ok (), kyber')) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let enc := E2E.Record.encSession (Over.clearPending s)
    let oneTime' := match pm.preKeyId with
      | none => StoresGhost.opened.oneTime
      | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
    let g' : StoresGhost :=
      { StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := oneTime'
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1 ses' enc) }
    (Over.encodeRecordPrev1 ses' enc).length < 2 ^ 32 ∧
      decPkOverDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) := by
  subst hmsg_i
  let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
  have hmsg : (pmOfE m pm.message).message = pm.message :=
    (pmOfE_fields m pm.message).2.2.2.2.2.2.1
  have hok1 : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk)).1 = .ok pt := by rw [hok]
  have hok2 : (GenP3.genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W meE k m dk)).2 = st' := by rw [hok]
  have hLen := encodeRecordPrev1_pathCOver_lt_32 hd0 hIn hcur hver hok1
  dsimp only at hLen
  rw [hok2] at hLen
  have hDec : decPkOverDef X W Scope F peer.val me.val pm coins =
      some (some ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1
            { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }
            (E2E.Record.encSession (Over.clearPending s))) }, pt)) := by
    unfold decPkOverDef
    rw [hload]
    dsimp only [Option.bind_some]
    rw [htrust]
    dsimp only
    rw [hcur]
    dsimp only
    rw [ite_eq_right hnot, hpk]
    dsimp only
    rw [hk, hkp, hreg]
    dsimp only
    rw [recvPrekeyState_of_accept_some X W (initParty peer.val) meE k m pm.message
      (pkRecvCoins coins) hi (pkStoreKeys_ids_eq hk) hacc]
    have ht := tryDecryptFromRecord_preKey_ver_eq (coins := coins)
      (st := pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk) hd0 (hmsg ▸ hver)
    rw [hmsg] at ht
    rw [ht, hok]
    dsimp only
    rw [hmark]
    rfl
  have hky' : kyber' =
      (StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey).2 := by
    rw [hmark]
  have hWr : ∀ pw ∈ ({ StoresGhost.opened with
        identity := StoresGhost.opened.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        kyber := kyber'
        oneTime := match pm.preKeyId with
          | none => StoresGhost.opened.oneTime
          | some j => (Cli.removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
        sessions := StoresGhost.opened.sessions.put (Cli.addressText peer.val)
          (Over.encodeRecordPrev1
            { pathAInitSession W meE k m dk with
              state := st', pendingPreKey := none, pendingKyberPreKey := none }
            (E2E.Record.encSession (Over.clearPending s))) } : StoresGhost).writes,
      cliWrOk pw.1 := by
    rw [hky']
    exact storesWrOk_pathA hf
  exact ⟨hLen, hDec, hWr⟩

theorem decPkOverDef_of_untrusted (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (huntr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok false) :
    decPkOverDef X W Scope F peer me pm coins = decPkDef X W Scope F peer me pm coins := by
  unfold decPkOverDef decPkDef
  rcases Slots.loadRec Scope F peer with _ | (_ | r) <;> simp [huntr]

end LibsignalBinary.Proofs.SignalSession.Cli.D3
