/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Stmt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Lemmas.Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Pure Matched-Session (Path B) Model and Store Agreement

Proves coins, version, and `recordError` bridges, generic `.preKey` `RecOk` preservation
(`tryDecryptFromRecord_preKey_recOk_of_scopeIn`), and matched-session (`Path B`) `decPkDef`
branch agreement.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Coins, Version, and `recordError` Helpers -/

theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {t e : α} (hc : c) :
    (if c then t else e) = t := by
  split <;> [rfl; contradiction]

theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {t e : α} (hc : ¬ c) :
    (if c then t else e) = e := by
  split <;> [contradiction; rfl]

private theorem take_append_replicate_le {α : Type} (b : α) :
    ∀ (c : List α) (k n : Nat), k ≤ n →
      (c ++ List.replicate n b).take k = c.take k ++ List.replicate (k - c.length) b
  | [], k, n, hkn => by
    simp [Nat.min_eq_left hkn]
  | _ :: _, 0, _, _ => by simp
  | x :: xs, k + 1, n, hkn => by
    have hk : k ≤ n := Nat.le_of_succ_le hkn
    simp only [List.cons_append, List.take_succ_cons, List.length_cons,
      Nat.succ_sub_succ_eq_sub, take_append_replicate_le b xs k n hk]

/-- `coinsOf c` (`(c ++ replicate 32 0).take 32`) equals `pkRecvCoins c`. -/
theorem coinsOf_eq_pkRecvCoins (c : List (BitVec 8)) :
    LibsignalTripleRatchetRepr.coinsOf c = pkRecvCoins c := by
  unfold LibsignalTripleRatchetRepr.coinsOf pkRecvCoins
  rw [take_append_replicate_le 0#8 c 32 32 (Nat.le_refl 32)]

/-- `st.version.toNat = msg.messageVersion.toNat` iff `st.version = msg.messageVersion.zeroExtend 32`. -/
theorem version_eq_zeroExtend_iff (st : SessionState (List (BitVec 8))) (msg : SignalMessage) :
    st.version.toNat = msg.messageVersion.toNat ↔
      st.version = msg.messageVersion.zeroExtend 32 := by
  have hz : (msg.messageVersion.zeroExtend 32).toNat = msg.messageVersion.toNat := by
    simp [BitVec.toNat_setWidth]; omega
  constructor
  · intro h
    exact BitVec.eq_of_toNat_eq (h.trans hz.symm)
  · intro h
    exact (congrArg BitVec.toNat h).trans hz

theorem version_ne_zeroExtend_iff (st : SessionState (List (BitVec 8))) (msg : SignalMessage) :
    st.version.toNat ≠ msg.messageVersion.toNat ↔
      st.version ≠ msg.messageVersion.zeroExtend 32 :=
  not_congr (version_eq_zeroExtend_iff st msg)

/-- `SessionState.recordError` produces `.panic` iff the input error is `.panic`. -/
theorem recordError_eq_panic_iff (msgType : MessageType) (e : SignalProtocolError) :
    SessionState.recordError msgType e = .panic ↔ e = .panic :=
  match e with
  | .invalidSessionStructure _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidKeyAgreement => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .duplicatedMessage _ _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidMessage _ _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidState => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .ciphertextMessageTooShort _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .legacyCiphertextVersion _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .unrecognizedCiphertextVersion _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .invalidProtobufEncoding => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .noKeyTypeIdentifier => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .badKeyType _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .badKeyLength _ => ⟨SignalProtocolError.noConfusion, SignalProtocolError.noConfusion⟩
  | .panic => Iff.rfl

/-! ## 2. Generic `.preKey` `RecOk` Preservation (`scopeIn` → `scopeKit` + `< 2^32`) -/

private theorem stripPq_bounded_of_parts' {s : Session (List (BitVec 8))}
    (hseeds : SeedsLen32 s.state)
    (hrc : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrep : CryptoVerification.E2E.Reach.SessRepr s.state)
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (hk : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569)
    (ha : s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33) :
    CryptoVerification.E2E.RecordX.DeserializeScopeBounded ⟨some (Slots.PqValid.stripPq s)⟩ := by
  have hscP : CryptoVerification.E2E.RecordX.SessionScopeP (Slots.PqValid.stripPq s) :=
    ⟨hrc, hp, hk, ha⟩
  refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq s, rfl,
    CryptoVerification.E2E.RecordX.sessionScopeBounded_of_sessionScopeP hscP⟩
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hseeds, Nat.lt_of_le_of_lt hrc (by decide), fun k hk' => ?_⟩
    rw [hk k hk']; decide
  · intro t ht
    injection ht with ht; subst ht
    rfl
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hrep.1, hrep.2, hwf, ?_⟩
    dsimp only [Slots.PqValid.stripPq]
    rcases ha with ha | ha <;> rw [ha] <;> decide

/-- One successful `SessionState.tryDecryptFromRecord` step at `pqxdhSpqrSession W` (`= (pqxdhSpqrModel W).spqr` on
decrypt) with message type `.preKey` maps any `Slots.scopeIn` session `ses` to a cleared session
in `Slots.scopeKit` whose canonical encoding is shorter than `2 ^ 32` bytes. -/
theorem tryDecryptFromRecord_preKey_recOk_of_scopeIn
    {W : PEParams} {expected : Option (List (BitVec 8))}
    {msg : SignalMessage} {rc : BitVec 256}
    {ses : Session (List (BitVec 8))} {st' : SessionState (List (BitVec 8))}
    {pt : List (BitVec 8)}
    (hIn : Slots.scopeIn ⟨some ses⟩)
    (hTry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      expected msg .preKey rc ses.state = (.ok pt, st')) :
    let ses' : Session (List (BitVec 8)) :=
      { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    Slots.scopeKit ⟨some ses'⟩ ∧ (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  have hTryV1 : SessionState.tryDecryptFromRecord W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state = (.ok pt, st') := hTry
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses₀, hCur₀, hSessSc⟩ := hIn
  injection hCur₀ with hses; subst hses
  obtain ⟨hSeeds, _, _⟩ := hInP ses rfl
  have hPqSes : Slots.PqValid.PqInV1 ses.state.pqRatchetState := hPqIn ses rfl
  obtain ⟨hRep1, hRep2, _, _⟩ := hRep ses rfl
  obtain ⟨hRC, _, _, hAbk⟩ := hSessSc
  obtain ⟨hSeeds', hRC', _, _, key, hRecv⟩ :=
    CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state st' pt hSeeds hRC hTryV1
  have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
    CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      expected msg .preKey rc ses.state st' pt ⟨hRep1, hRep2⟩ hTryV1
  have hPqOut : Slots.PqValid.PqOutV1 st'.pqRatchetState :=
    (Slots.PqValid.pqStep_spqrV1 W.C.F W.Q.K).recv ses.state.pqRatchetState msg.pqRatchet
      st'.pqRatchetState key hPqSes hRecv
  have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
    (Slots.PqValid.pqStep_spqrV1 W.C.F W.Q.K).out_bound st'.pqRatchetState hPqOut
  have hPendFalse : st'.pendingPreKey = false :=
    (SessionState.tryDecryptFromRecord_ok W.C (pqxdhSpqrSession W) expected msg .preKey rc hTry).1
  let ses' : Session (List (BitVec 8)) :=
    { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
  have hWf' : ses'.Wf := by
    unfold Session.Wf; dsimp only [ses']; exact hPendFalse
  have hPendTs' : ∀ p, ses'.pendingPreKey = some p → p.timestamp = 0 := fun _ hp => by cases hp
  have hKyber' : ∀ k, ses'.pendingKyberPreKey = some k → k.ciphertext.length = 1569 :=
    fun _ hk => by cases hk
  have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
    ⟨hRC', hPendTs', hKyber', hAbk⟩
  have hKit' : Slots.scopeKit ⟨some ses'⟩ := by
    refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
    · intro s hs; injection hs with hs; subst hs
      exact ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun _ hk => by cases hk⟩
    · intro s hs; injection hs with hs; subst hs
      exact hPqLt
    · intro s hs; injection hs with hs; subst hs
      refine ⟨hRep'.1, hRep'.2, hWf', ?_⟩
      dsimp only [ses']
      rcases hAbk with ha | ha <;> rw [ha] <;> decide
  have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq ses')⟩ :=
    stripPq_bounded_of_parts' hSeeds' hRC' hRep' hWf' hPendTs' hKyber' hAbk
  exact ⟨hKit', Slots.PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

/-! ## 3. Address Serialization & `tryDecryptFromRecord` ↔ `genP3S5Model` -/

theorem serializeAddresses_eq_expectedAddrs {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm) :
    serializeAddresses (serviceIdParse uuidTryParse) peer me =
      (pqxdhSessionParams W).expectedAddrs (initParty peer.val) := by
  obtain ⟨P, hpeer, hme⟩ := hd.party
  have hp : initParty peer.val = P := by
    unfold initParty
    rw [hpeer]
    exact InitS0.initParty_eq P
  have hconv : serializeAddresses (serviceIdParse uuidTryParse) peer me =
      serializeAddrVals (serviceIdParse uuidTryParse) peer.val me.val := rfl
  rw [hconv, hp, hpeer, hme, Agree.serializeAddrVals_expectedAddrs_pq]

theorem tryDecryptFromRecord_preKey_ver_ne {W : PEParams}
    {expected : Option (List (BitVec 8))} {msg : SignalMessage} {rc : BitVec 256}
    {st : SessionState (List (BitVec 8))}
    (hver : st.version ≠ msg.messageVersion.zeroExtend 32) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) expected msg .preKey rc st =
      (.error (.invalidMessage .preKey .decryptionFailed), st) := by
  unfold SessionState.tryDecryptFromRecord
  have hne : st.version.toNat ≠ msg.messageVersion.toNat :=
    (version_ne_zeroExtend_iff st msg).mpr hver
  rw [ite_pos hne]

theorem tryDecryptFromRecord_preKey_ver_eq {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {st : SessionState (List (BitVec 8))}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hver : st.version = pm.message.messageVersion.zeroExtend 32) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st =
    match genP3S5Model W.C W.Q.K peer me pm.message coins st with
    | (.ok ptext, updated) => (.ok ptext, updated)
    | (.error e, _) => (.error (SessionState.recordError .preKey e), st) := by
  rw [← Agree.tryDecrypt_spqrV1W_eq_spqrPq, ← serializeAddresses_eq_expectedAddrs hd,
    ← coinsOf_eq_pkRecvCoins coins]
  have hspqr : (pqxdhSpqrModel W).spqr = (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr := rfl
  rw [hspqr]
  unfold SessionState.tryDecryptFromRecord genP3S5Model
  have hnot_ne : ¬ (st.version.toNat ≠ pm.message.messageVersion.toNat) :=
    not_not.mpr ((version_eq_zeroExtend_iff st pm.message).mpr hver)
  rw [ite_neg hnot_ne]
  rcases (SessionState.tryDecryptWithState W.C
    (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
    (serializeAddresses (serviceIdParse uuidTryParse) peer me) pm.message .preKey
    (LibsignalTripleRatchetRepr.coinsOf coins)).exec st with ⟨_ | _, _⟩ <;> rfl

/-! ## 4. Matched-Session (Path B) Scope Pinning & `decPkDef` Branch Lemmas -/

theorem scope_of_loadRec_some {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal} {r : SessionRecord (List (BitVec 8))}
    (hf : Slots.FilesOkPeer Scope F peer)
    (hload : Slots.loadRec Scope F peer = .ok (some r)) :
    Scope r := by
  have hans := Slots.sessLoadAns_loadRec hf
  rw [hload] at hans
  rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (Cli.addressText peer) with _ | bs
  · rw [hget] at hans; cases hans
  · cases bs with
    | nil => rw [hget] at hans; cases hans
    | cons b bs' =>
      rw [hget] at hans
      obtain ⟨r', hr', _, hsc⟩ := hans
      injection hr' with hr'
      injection hr' with hr'
      subst hr'
      exact hsc

theorem pathB_scopeIn_and_match {A : RustAlloc} {b : BitVec 64}
    {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {pm : PreKeySignalMessage}
    {s1 s2 s3 s4 : Nat} {r : SessionRecord (List (BitVec 8))}
    {s : Session (List (BitVec 8))}
    (hinjK : Slots.EncodeInjOn Slots.scopeKit)
    (hsub : ∀ r', Scope r' → Slots.scopeIn r')
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload_rel : (cliSessionStoreSpec A b cliIo.rd F cliWrOk Slots.scopeKit peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s) :
    Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩) ∧
      r = ⟨some s⟩ ∧
      Slots.scopeIn ⟨some s⟩ ∧
      SessMatchesPm s pm ∧
      pm.messageVersion = 4#8 ∧
      s.state.version = 4#32 ∧
      SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      s.state.pqRatchetState.length < 2 ^ 32 := by
  have hr_eq : r = ⟨some s⟩ := by cases r; simpa using hcur
  subst hr_eq
  have hloadK : (.ok (some ⟨some s⟩)) = Slots.loadRec Slots.scopeKit F peer.val :=
    Slots.cliSessLoadRel_eq_loadRec hinjK hload_rel
  have hloadS : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩) :=
    (loadRec_scopeKit_eq hinjK hsub hf).symm.trans hloadK.symm
  have hIn : Slots.scopeIn ⟨some s⟩ := hsub _ (scope_of_loadRec_some hf hloadS)
  have hMatch : SessMatchesPm s pm := hd.sessMatch ⟨some s⟩ s hloadS rfl
  have hmVer : pm.messageVersion = 4#8 := by
    obtain ⟨m, i, _, _, rfl⟩ := hd.typed
    rfl
  have hsVer : s.state.version = 4#32 := by
    rw [hMatch.1, hmVer]
    rfl
  obtain ⟨hSeeds, hRC, _⟩ := hIn.1.1 s rfl
  have hPqLt : s.state.pqRatchetState.length < 2 ^ 32 :=
    Slots.scopeKit_pqrState_lt (Slots.scopeKit_of_scopeIn hIn) s rfl
  exact ⟨hloadS, rfl, hIn, hMatch, hmVer, hsVer, hSeeds, hRC, hPqLt⟩

theorem decPkDef_pathB_remId_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope F peer = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity ≠ some pm.identityKey) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [ite_pos hmatch, ite_pos hrem]

theorem decPkDef_pathB_ver_ne (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope F peer = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version ≠ pm.message.messageVersion.zeroExtend 32) :
    decPkDef X W Scope F peer me pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [ite_pos hmatch, ite_neg (not_not.mpr hrem), tryDecryptFromRecord_preKey_ver_ne hver]

theorem decPkDef_pathB_panic (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hpan : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [ite_pos hmatch, ite_neg (not_not.mpr hrem), tryDecryptFromRecord_preKey_ver_eq hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st'⟩
  rw [hm] at hpan
  dsimp only at hpan
  subst hpan
  rfl

theorem decPkDef_pathB_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {e : SignalProtocolError}
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (herr : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .error e)
    (hne : e ≠ .panic) :
    decPkDef X W Scope F peer.val me.val pm coins = some none := by
  dsimp only [decPkDef]
  rw [hload]
  dsimp only [Option.bind_some]
  rw [htrust]
  dsimp only
  rw [ite_pos hmatch, ite_neg (not_not.mpr hrem), tryDecryptFromRecord_preKey_ver_eq hd hver]
  rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st'⟩
  rw [hm] at herr
  dsimp only at herr
  subst herr
  dsimp only
  have hrec_ne : SessionState.recordError .preKey e ≠ .panic :=
    mt (recordError_eq_panic_iff .preKey e).mp hne
  cases hr : SessionState.recordError .preKey e <;> first | exact absurd hr hrec_ne | rfl

theorem decPkDef_pathB_ok (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrGhost) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {s : Session (List (BitVec 8))} {pt : List (BitVec 8)}
    (hf : Slots.FilesOkPeer Scope F peer.val)
    (hd : DecPkOk₀ W Scope F peer.val me.val pm)
    (hIn : Slots.scopeIn ⟨some s⟩)
    (hload : Slots.loadRec Scope F peer.val = .ok (some ⟨some s⟩))
    (htrust : StoresGhost.opened.identity.trusted cliIo.rd F peer.val pm.identityKey = .ok true)
    (hmatch : SessMatchesPm s pm)
    (hrem : s.state.remoteIdentity = some pm.identityKey)
    (hver : s.state.version = pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).1 = .ok pt) :
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins s.state).2
    let ses' : Session (List (BitVec 8)) :=
      { s with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    let g := StoresGhost.opened
    let g' : StoresGhost :=
      { g with
        identity := g.identity.saveUpd cliIo.rd F peer.val pm.identityKey
        sessions := g.sessions.put (Cli.addressText peer.val) (E2E.Record.encodeRecord ⟨some ses'⟩) }
    decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) ∧
      (∀ pw ∈ g'.writes, cliWrOk pw.1) ∧
      Slots.scopeKit ⟨some ses'⟩ ∧
      (E2E.Record.encodeRecord ⟨some ses'⟩).length < 2 ^ 32 := by
  intro st' ses' g g'
  have hTry : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) s.state = (.ok pt, st') := by
    rw [tryDecryptFromRecord_preKey_ver_eq hd hver]
    dsimp only [st']
    rcases hm : genP3S5Model W.C W.Q.K peer me pm.message coins s.state with ⟨res, st1⟩
    rw [hm] at hok
    dsimp only at hok
    subst hok
    rfl
  have hDec : decPkDef X W Scope F peer.val me.val pm coins = some (some (g', pt)) := by
    dsimp only [decPkDef]
    rw [hload]
    dsimp only [Option.bind_some]
    rw [htrust]
    dsimp only
    rw [ite_pos hmatch, ite_neg (not_not.mpr hrem), hTry]
  have hRecOk := tryDecryptFromRecord_preKey_recOk_of_scopeIn hIn hTry
  exact ⟨hDec, storesWrOk_pathB hf, hRecOk.1, hRecOk.2⟩

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
