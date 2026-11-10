/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs

/-!
# D2(c) Domain Precondition (`DecPkOkD2c`) and Model (`decPkDefD2c`) for Non-Matching Pre-Key Messages

Extends `DecryptPrekey/S0.lean` to non-matching current sessions (`D2(c)`):
- `DecPkOkD2c W Scope F peer me pm` weakens `DecPkOk₀.sessMatch` to `sessVer4` (every loaded current
  session has `s.state.version = 4#32`, satisfied by all reachable `PqxdhPartyInSpecDomain` states).
- `decPkDefD2c X W Scope F peer me pm coins` agrees with `decPkDef` when no current session exists
  or when `SessMatchesPm s pm` holds, and on `¬ SessMatchesPm s pm` runs the PQXDH responder path
  and stores the 2-session record archiving `Over.clearPending s` behind the newly promoted session.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

/-- D2(c) file precondition for `decrypt_prekey`: identical to `DecPkOk₀` except `sessMatch` is
weakened to `sessVer4` (every loaded current session has protocol version `4`, which holds for all
reachable `PqxdhPartyInSpecDomain` sessions regardless of whether `alice_base_key` matches `pm`). -/
structure DecPkOkD2c (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop where
  party : ∃ P : Party, peer = RunRefine.addrValE P.other ∧ me = RunRefine.addrValE P
  typed : ∃ (m : PreKeyMessageFields) (i : SignalMessage), m.inner.length + 2048 < 2 ^ 32 ∧
    SignalMessage.tryFrom protoSignalCodec m.inner = .ok i ∧ pm = pmOfE m i
  sessVer4 : ∀ r s, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = some s →
    s.state.version = 4#32
  distinctAcct : ¬ SameServiceId peer me
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  idPairDerived : ∀ kp, StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp →
    kp.identityKey.publicKey = (keyPairOf W.C kp.privateKey.bytes).publicKey
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

/-- Shared PQXDH responder accept & store continuation parameterized by the session-record byte
encoder `mkBytes x gs`. -/
noncomputable def decPkAcceptWith (X : UnreachedPqxdhPrimitives) (W : PEParams) (F : FsFiles) (peer : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8)) (saved : IdGhost)
    (mkBytes : RecordExtras → GhostState (List (BitVec 8)) → List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  let g := StoresGhost.opened
  let P := initParty peer
  match pkToE? pm with
  | none => some none
  | some m =>
    match pkStoreKeys F m, g.identity.keyPair cliIo.rd F, g.identity.regId cliIo.rd F with
    | some k, .ok kp, .ok reg =>
      match recvPrekeyState X W P ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
      | none => none
      | some none => some none
      | some (some (x, gs, pt)) =>
        match g.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
        | (.error _, _) => some none
        | (.ok (), kyber') =>
          let oneTime' := match pm.preKeyId with
            | none => g.oneTime
            | some j => (removePreKey cliIo.rd F g.oneTime j).2
          some (some ({ g with
            identity := saved
            kyber := kyber'
            oneTime := oneTime'
            sessions := g.sessions.put (addressText peer) (mkBytes x gs) },
            pt))
    | _, _, _ => some none

/-- Extended `decrypt_prekey` model covering D2(c) (`S_d2c.decryptPrekey`):
* `r.bind (·.currentSession) = none`: PQXDH accept storing `encodeRecordUnderExtras (fun _ => x) gs` (Path A);
* `r.bind (·.currentSession) = some s` with `SessMatchesPm s pm`: in-place decrypt on `s` (Path B);
* `r.bind (·.currentSession) = some s` with `¬ SessMatchesPm s pm`: PQXDH accept archiving
  `Over.clearPending s` in field 2 behind the newly promoted session in field 1 (Path C / D2(c)). -/
noncomputable def decPkDefD2c (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer _me : AddrVal)
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
          if s.state.remoteIdentity ≠ some pm.identityKey then some none
          else
            match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P)
                pm.message .preKey (pkRecvCoins coins) s.state with
            | (.ok pt, st) =>
              some (some ({ g with
                identity := saved
                sessions := g.sessions.put (addressText peer)
                  (E2E.Record.encodeRecord
                    { currentSession := some { s with state := st, pendingPreKey := none,
                                                      pendingKyberPreKey := none } }) }, pt))
            | (.error .panic, _) => none
            | (.error _, _) => some none
        else
          decPkAcceptWith X W F peer pm coins saved (fun x gs =>
            encodeRecordUnderExtras (fun _ => x) gs ++
              E2E.Record.lenField 2 (E2E.Record.encSession (Over.clearPending s)))
      | none =>
        decPkAcceptWith X W F peer pm coins saved (fun x gs => encodeRecordUnderExtras (fun _ => x) gs)

/-! ## Bridging `DecPkOkD2c` / `decPkDefD2c` to `DecPkOk₀` / `decPkDef` on Paths A and B -/

/-- On `pmOfE m i`, `pm.messageVersion = 4`, so `DecPkOk₀` implies `DecPkOkD2c`. -/
theorem DecPkOk₀.toDecPkOkD2c {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (h : DecPkOk₀ W Scope F peer me pm) :
    DecPkOkD2c W Scope F peer me pm := by
  refine ⟨h.party, h.typed, ?_, h.distinctAcct, h.keyPairLt, h.idPairDerived, h.preKeysWf,
    h.baseKeysLt⟩
  intro r s hload hcur
  have hm := (h.sessMatch r s hload hcur).1
  obtain ⟨m, i, _, _, rfl⟩ := h.typed
  simpa [pmOfE, E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel] using hm

/-- When `loadRec` returns `.ok none` (or `.ok (some ⟨none⟩)`), `DecPkOkD2c` upgrades to `DecPkOk₀`
because `sessMatch` is vacuous. -/
theorem DecPkOkD2c.toDecPkOk₀_of_noCurrent {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (h : DecPkOkD2c W Scope F peer me pm)
    (hnone : ∀ r, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = none) :
    DecPkOk₀ W Scope F peer me pm := by
  refine ⟨h.party, h.typed, ?_, h.distinctAcct, h.keyPairLt, h.idPairDerived, h.preKeysWf,
    h.baseKeysLt⟩
  intro r s hload hcur
  rw [hnone r hload] at hcur
  cases hcur

/-- When `loadRec` returns `.ok (some r)` with `r.currentSession = some s` and `SessMatchesPm s pm`,
`DecPkOkD2c` upgrades to `DecPkOk₀`. -/
theorem DecPkOkD2c.toDecPkOk₀_of_match {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {r0 : SessionRecord (List (BitVec 8))}
    {s0 : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (h : DecPkOkD2c W Scope F peer me pm)
    (hload0 : Slots.loadRec Scope F peer = .ok (some r0))
    (hcur0 : r0.currentSession = some s0)
    (hmatch : SessMatchesPm s0 pm) :
    DecPkOk₀ W Scope F peer me pm := by
  refine ⟨h.party, h.typed, ?_, h.distinctAcct, h.keyPairLt, h.idPairDerived, h.preKeysWf,
    h.baseKeysLt⟩
  intro r s hload hcur
  rw [hload0] at hload
  injection hload with hr
  injection hr with hr
  subst hr
  rw [hcur0] at hcur
  injection hcur with hs
  subst hs
  exact hmatch

/-- On a `DecPkOkD2c` call where `¬ SessMatchesPm s pm`, `s.state.version = 4#32` and `pm`'s
version is `4`, so `s.aliceBaseKey ≠ pm.baseKey.serialize`. -/
theorem DecPkOkD2c.aliceBaseKey_ne_of_not_match {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {r : SessionRecord (List (BitVec 8))}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (h : DecPkOkD2c W Scope F peer me pm)
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (hnot : ¬ SessMatchesPm s pm) :
    s.state.version = 4#32 ∧ s.aliceBaseKey ≠ pm.baseKey.serialize := by
  have hver := h.sessVer4 r s hload hcur
  refine ⟨hver, fun hbk => hnot ⟨?_, hbk⟩⟩
  obtain ⟨m, i, _, _, rfl⟩ := h.typed
  simpa [pmOfE, E2E.Pqxdh.ResponderWire.PreKeyTryFromArgs.toModel] using hver

/-- `Slots.loadRec (fun _ => False)` can never succeed with `some r`. -/
theorem loadRec_false_ne_some (F : FsFiles) (peer : AddrVal)
    (r : SessionRecord (List (BitVec 8))) :
    Slots.loadRec (fun _ => False) F peer ≠ .ok (some r) := by
  unfold Slots.loadRec
  cases StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) with
  | error _ => intro h; cases h
  | ok bs =>
    cases bs with
    | nil => intro h; cases h
    | cons b rest =>
      dsimp only
      split
      · rename_i hEx
        rcases hEx with ⟨_, _, hf⟩
        exact False.elim hf
      · intro h; cases h

/-- Any `DecPkOkD2c` upgrades unconditionally to `DecPkOk₀` at the empty scope `fun _ => False`
(discharging all `Scope`-independent invariants such as `cliIdOwnInv_opened`, `cliPkInv_opened`,
`cliSpkInv_opened`, `cliKpkInvFull_opened`, `distinctSid_of_decPkOk₀`, and
`tryDecryptFromRecord_preKey_ver_eq`). -/
theorem DecPkOkD2c.toDecPkOk₀_vacuous {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    (h : DecPkOkD2c W Scope F peer me pm) :
    DecPkOk₀ W (fun _ => False) F peer me pm where
  party := h.party
  typed := h.typed
  sessMatch := fun r _ hload _ => False.elim (loadRec_false_ne_some F peer r hload)
  distinctAcct := h.distinctAcct
  keyPairLt := h.keyPairLt
  idPairDerived := h.idPairDerived
  preKeysWf := h.preKeysWf
  baseKeysLt := h.baseKeysLt

/-- When `loadRec` fails or yields no current session, `decPkDefD2c` equals `decPkDef`. -/
theorem decPkDefD2c_eq_decPkDef_of_noCurrent (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (hnone : ∀ r, Slots.loadRec Scope F peer = .ok (some r) → r.currentSession = none) :
    decPkDefD2c X W Scope F peer me pm coins = decPkDef X W Scope F peer me pm coins := by
  have hAccept : ∀ saved,
      decPkAcceptWith X W F peer pm coins saved (fun x gs => encodeRecordUnderExtras (fun _ => x) gs) =
        match pkToE? pm with
        | none => some none
        | some m =>
          match pkStoreKeys F m, StoresGhost.opened.identity.keyPair cliIo.rd F,
              StoresGhost.opened.identity.regId cliIo.rd F with
          | some k, .ok kp, .ok reg =>
            match recvPrekeyState X W (initParty peer) ⟨kp.privateKey.bytes, reg⟩ k m
                (pkRecvCoins coins) with
            | none => none
            | some none => some none
            | some (some (x, gs, pt)) =>
              match StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId pm.signedPreKeyId pm.baseKey with
              | (.error _, _) => some none
              | (.ok (), kyber') =>
                some (some ({ StoresGhost.opened with
                  identity := saved
                  kyber := kyber'
                  oneTime := match pm.preKeyId with
                    | none => StoresGhost.opened.oneTime
                    | some j => (removePreKey cliIo.rd F StoresGhost.opened.oneTime j).2
                  sessions := StoresGhost.opened.sessions.put (addressText peer)
                    (encodeRecordUnderExtras (fun _ => x) gs) }, pt))
          | _, _, _ => some none := by
    intro _
    rfl
  unfold decPkDefD2c decPkDef
  dsimp only
  cases hload : Slots.loadRec Scope F peer with
  | error _ => rfl
  | ok opt =>
    dsimp only
    cases StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey with
    | error _ => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        cases opt with
        | none =>
          dsimp only [Option.bind_none]
          exact hAccept _
        | some r =>
          dsimp only [Option.bind_some]
          rw [hnone r hload]
          exact hAccept _

/-- When `loadRec` yields `some r` with `r.currentSession = some s` and `SessMatchesPm s pm`,
`decPkDefD2c` equals `decPkDef`. -/
theorem decPkDefD2c_eq_decPkDef_of_match (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (hmatch : SessMatchesPm s pm) :
    decPkDefD2c X W Scope F peer me pm coins = decPkDef X W Scope F peer me pm coins := by
  unfold decPkDefD2c decPkDef
  dsimp only
  rw [hload]
  dsimp only
  cases StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey with
  | error _ => rfl
  | ok b =>
    cases b with
    | false => rfl
    | true =>
      dsimp only [Option.bind_some]
      rw [hcur]
      dsimp only
      have hite1 : ∀ {α : Type} [Decidable (SessMatchesPm s pm)] (t e : α),
          (@ite α (SessMatchesPm s pm) ‹_› t e) = t := by
        intro α _ t e; split <;> [rfl; contradiction]
      rw [hite1, hite1]
      by_cases hrem : s.state.remoteIdentity ≠ some pm.identityKey
      · simp [hrem]
      · simp only [hrem, ↓reduceIte]
        rcases SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs (initParty peer)) pm.message .preKey
            (pkRecvCoins coins) s.state with ⟨err | pt, st⟩
        · cases err <;> rfl
        · rfl

/-- When `loadRec` returns `.error`, `decPkDefD2c` rejects (`some none`). -/
theorem decPkDefD2c_of_load_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8)) {e : Unit}
    (hload : Slots.loadRec Scope F peer = .error e) :
    decPkDefD2c X W Scope F peer me pm coins = some none := by
  simp [decPkDefD2c, hload]

/-- When `identity.trusted` returns `.error` or `.ok false`, `decPkDefD2c` equals `decPkDef`
(both reject with `some none`). -/
theorem decPkDefD2c_eq_decPkDef_of_untrusted (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (huntr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey ≠ .ok true) :
    decPkDefD2c X W Scope F peer me pm coins = decPkDef X W Scope F peer me pm coins := by
  unfold decPkDefD2c decPkDef
  dsimp only
  cases Slots.loadRec Scope F peer with
  | error _ => rfl
  | ok _ =>
    dsimp only
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey with
    | error _ => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true => exact absurd htr huntr

/-! ## Encoding equivalences for the archived 2-session record -/

/-- `encodeRecordUnderExtras (fun _ => x) gs ++ lenField 2 prevEnc` equals
`Over.encodeRecordPrev1 (sessionOfX (fun _ => x) gs) prevEnc`. -/
theorem encodeRecordX_append_lenField2_eq_encodeRecordPrev1
    (x : RecordExtras) (gs : GhostState (List (BitVec 8))) (prevEnc : List (BitVec 8)) :
    encodeRecordUnderExtras (fun _ => x) gs ++ E2E.Record.lenField 2 prevEnc =
      Over.encodeRecordPrev1 (E2E.RecordX.sessionOfX (fun _ => x) gs) prevEnc := by
  rw [E2E.RecordX.encodeRecordX_eq_toRecord, E2E.RecordX.toRecord_extrasOf_eq]
  rfl

/-- Clearing pending pre-key fields on `sessionOfX (fun _ => x) g` encodes to
`encStateUnderExtras x { g.session with pendingPreKey := false }`. -/
theorem encSession_clearPending_sessionOfX_eq (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) :
    E2E.Record.encSession
        (Over.clearPending (E2E.RecordX.sessionOfX (fun _ => x) g)) =
      encStateUnderExtras x { g.session with pendingPreKey := false } := by
  unfold E2E.Record.encSession encStateUnderExtras E2E.RecordX.sessionOfX Over.clearPending
  rfl

/-- Full 2-session record bytes produced on D2(c) when archiving a domain session `(x₀, g₀)` and
promoting `(x', gs)`. -/
theorem d2c_record_bytes_eq (x' x₀ : RecordExtras)
    (gs g₀ : GhostState (List (BitVec 8))) :
    encodeRecordUnderExtras (fun _ => x') gs ++
        E2E.Record.lenField 2
          (E2E.Record.encSession
            (Over.clearPending (E2E.RecordX.sessionOfX (fun _ => x₀) g₀))) =
      E2E.Record.lenField 1 (encStateUnderExtras x' gs.session) ++
        E2E.Record.lenField 2 (encStateUnderExtras x₀ { g₀.session with pendingPreKey := false }) := by
  rw [encSession_clearPending_sessionOfX_eq]
  rfl

/-! ## Unfolding `decPkDefD2c` on Path C (`some s`, `¬ SessMatchesPm s pm`, `trusted = .ok true`) -/

theorem decPkDefD2c_of_not_match (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles) (peer me : AddrVal)
    (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    {r : SessionRecord (List (BitVec 8))}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hload : Slots.loadRec Scope F peer = .ok (some r))
    (hcur : r.currentSession = some s)
    (htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true)
    (hnot : ¬ SessMatchesPm s pm) :
    decPkDefD2c X W Scope F peer me pm coins =
      decPkAcceptWith X W F peer pm coins
        (StoresGhost.opened.identity.saveUpd cliIo.rd F peer pm.identityKey)
        (fun x gs =>
          encodeRecordUnderExtras (fun _ => x) gs ++
            E2E.Record.lenField 2 (E2E.Record.encSession (Over.clearPending s))) := by
  unfold decPkDefD2c
  simp [hload, hcur, htr, hnot]

end CryptoVerification.SignalSession.Cli.RunProofs
