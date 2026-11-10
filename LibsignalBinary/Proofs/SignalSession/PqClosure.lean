/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.PqStep
public import LibsignalBinary.Proofs.SignalSession.Closure.Promote
public import LibsignalBinary.Proofs.SignalSession.Closure.Version
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Hybrid
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.SecurityWith
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Party
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhCorrectModel
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.LibsignalE2E.State
public import LibsignalBinary.Specifications.LibsignalE2E.StateXModel
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RecordCodecs.Proto
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.SignalPqxdh.Model
public import LibsignalBinary.Specifications.SignalSession.PqDir
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Specifications.SignalSession.SmDir

/-!
# Domain Closure of `CliSpecPqxdh` Under Accepted Calls

Proves that `PqxdhPartyInSpecDomain W` is closed under accepted `PqStep` transitions (`wfPq_step`),
via `pqStep_lastResortUses_le` (at most one last-resort `.base-keys` entry appended per step) and
`reachPq_promote` (pre-key promotion preserves `ReachablePqxdhSession`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

private theorem map_lastResort_unchanged
    (l : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)))
    (kpkId : BitVec 32) (pair : BitVec 32 × List.Vector (BitVec 8) 32)
    (hni : kpkId ∉ l.map (·.1)) :
    l.map (fun (i, k, s) => if i = kpkId then (i, k, s ++ [pair]) else (i, k, s)) = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, k, s⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hni ⊢
    have hne : i ≠ kpkId := fun h => hni.1 h.symm
    simp only [hne, ↓reduceIte, ih hni.2]

private theorem map_lastResort_sum_le
    (l : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)))
    (kpkId : BitVec 32) (pair : BitVec 32 × List.Vector (BitVec 8) 32)
    (hnd : (l.map (·.1)).Nodup) :
    (((l.map fun (i, k, s) => if i = kpkId then (i, k, s ++ [pair]) else (i, k, s)).map
      fun e => e.2.2.length).sum) ≤
    (l.map fun e => e.2.2.length).sum + 1 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨i, k, s⟩
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases hi : i = kpkId
    · subst hi
      simp only [↓reduceIte, List.map_cons, List.sum_cons, List.length_append,
        List.length_singleton, map_lastResort_unchanged tl i pair hnd.1]
      omega
    · have htl := ih hnd.2
      simp only [List.map_cons, hi, ↓reduceIte, List.sum_cons]
      dsimp only at htl ⊢
      omega

private theorem markKyberUsed_eq_some (st st1 : PqParty) (m : PreKeyMessageFields)
    (h : markKyberUsed st m = some st1) :
    st1 = { st with kyberOneTime := st.kyberOneTime.map fun (i, k) =>
              if i = m.kpkId then (i, none) else (i, k) } ∨
    st1 = { st with kyberLastResort := st.kyberLastResort.map fun (i, k, s) =>
              if i = m.kpkId then (i, k, s ++ [(m.spkId, m.baseKey)]) else (i, k, s) } := by
  unfold markKyberUsed at h
  cases hko : List.lookup m.kpkId st.kyberOneTime with
  | none =>
    rw [hko] at h
    dsimp only at h
    cases hlr : List.lookup m.kpkId st.kyberLastResort with
    | none => rw [hlr] at h; cases h
    | some p =>
      rw [hlr] at h
      rcases p with ⟨_, seen⟩
      dsimp only at h
      by_cases hmem : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen
      · simp only [hmem, ↓reduceIte] at h; cases h
      · simp only [hmem, ↓reduceIte] at h
        cases h
        exact Or.inr rfl
  | some opt =>
    rw [hko] at h
    cases opt with
    | some _ =>
      cases h
      exact Or.inl rfl
    | none =>
      dsimp only at h
      cases hlr : List.lookup m.kpkId st.kyberLastResort with
      | none => rw [hlr] at h; cases h
      | some p =>
        rw [hlr] at h
        rcases p with ⟨_, seen⟩
        dsimp only at h
        by_cases hmem : 37 * seen.length > fileCapBytes ∨ (m.spkId, m.baseKey) ∈ seen
        · simp only [hmem, ↓reduceIte] at h; cases h
        · simp only [hmem, ↓reduceIte] at h
          cases h
          exact Or.inr rfl

private theorem pqInitModel_eq_some_some (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st st' : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (out : List (BitVec 8))
    (h : pqInitModel X W st b t = some (some (st', out))) :
    ∃ x g, initiateState X W st.party st.me b t = some (x, g) ∧
      st' = { st with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) } := by
  unfold pqInitModel at h
  cases htr : st.trusts ⟨⟨b.idPub⟩⟩ with
  | false => rw [htr] at h; simp only [Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    rw [htr] at h
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hinit : initiateState X W st.party st.me b t with
    | none => rw [hinit] at h; cases h
    | some xg =>
      rw [hinit] at h
      rcases xg with ⟨x, g⟩
      cases h
      exact ⟨x, g, rfl, rfl⟩

private theorem pqSendModel_eq_some_some (W : PEParams) (st st' : PqParty)
    (m r out : List (BitVec 8))
    (h : pqSendModel W st m r = some (some (st', out))) :
    ∃ x g msg s k, st.session = some (x, g) ∧
      SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session = (.ok msg, s) ∧
      st' = { st with peerId := some k, session := some (x, { g with session := s }) } := by
  unfold pqSendModel at h
  cases hs : st.session with
  | none => rw [hs] at h; cases h
  | some xg =>
    rw [hs] at h
    rcases xg with ⟨x, g⟩
    dsimp only at h
    rcases henc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with ⟨res, s⟩
    rw [henc] at h
    cases res with
    | error err => cases err <;> cases h
    | ok msg =>
      dsimp only at h
      cases hrem : g.session.remoteIdentity with
      | none => rw [hrem] at h; cases h
      | some k =>
        rw [hrem] at h
        dsimp only at h
        cases htr : st.trusts k with
        | false => rw [htr] at h; simp only [Bool.not_false, ↓reduceIte] at h; cases h
        | true =>
          rw [htr] at h
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          cases h
          exact ⟨x, g, msg, s, k, rfl, henc, rfl⟩

private theorem pqRecvWhisperModel_eq_some_some (W : PEParams) (st st' : PqParty)
    (c : List (BitVec 8)) (rc : BitVec 256) (out : List (BitVec 8))
    (h : pqRecvWhisperModel W st c rc = some (some (st', out))) :
    ∃ x g msg pt s k, st.session = some (x, g) ∧
      SignalMessage.tryFrom protoSignalCodec c = .ok msg ∧
      SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session = (.ok pt, s) ∧
      st' = { st with peerId := some k, session := some (x, { g with session := s }) } := by
  unfold pqRecvWhisperModel pqxdhSessionDecryptModel at h
  cases hs : st.session with
  | none => rw [hs] at h; cases h
  | some xg =>
    rw [hs] at h
    rcases xg with ⟨x, g⟩
    dsimp only at h
    cases htry : SignalMessage.tryFrom protoSignalCodec c with
    | error _ => rw [htry] at h; cases h
    | ok msg =>
      rw [htry] at h
      dsimp only at h
      rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨res, s⟩
      rw [hdec] at h
      cases res with
      | error err => cases err <;> cases h
      | ok pt =>
        dsimp only at h
        cases hrem : s.remoteIdentity with
        | none => rw [hrem] at h; cases h
        | some k =>
          rw [hrem] at h
          dsimp only at h
          cases htr : st.trusts k with
          | false => rw [htr] at h; simp only [Bool.not_false, ↓reduceIte] at h; cases h
          | true =>
            rw [htr] at h
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            cases h
            exact ⟨x, g, msg, out, s, k, rfl, rfl, hdec, rfl⟩

private theorem pqRecvPrekeyModel_eq_some_some (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st st' : PqParty) (m : PreKeyMessageFields) (rc : BitVec 256) (out : List (BitVec 8))
    (h : pqRecvPrekeyModel X W st m rc = some (some (st', out))) :
    (∃ x g inner pt s, st.session = some (x, g) ∧
      SignalMessage.tryFrom protoSignalCodec m.inner = .ok inner ∧
      SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session = (.ok pt, s) ∧
      st' = { st with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, { g with session := s }) }) ∨
    (∃ k x g pt st1, st.session = none ∧
      recvPrekeyState X W st.party st.me k m rc = some (some (x, g, pt)) ∧
      markKyberUsed st m = some st1 ∧
      st' = { removeOpk st1 m with peerId := some ⟨⟨m.idPub⟩⟩, session := some (x, g) }) := by
  unfold pqRecvPrekeyModel at h
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at h; cases h
  | ok inner =>
    rw [htry] at h
    dsimp only at h
    cases htr : st.trusts ⟨⟨m.idPub⟩⟩ with
    | false => rw [htr] at h; simp only [Bool.not_false, ↓reduceIte] at h; cases h
    | true =>
      rw [htr] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : st.session with
      | some xg =>
        rw [hs] at h
        rcases xg with ⟨x, g⟩
        dsimp only at h
        by_cases hmat : PqSessionMatches x g m
        · simp only [hmat, ↓reduceIte] at h
          by_cases hrem : g.session.remoteIdentity = some ⟨⟨m.idPub⟩⟩
          · simp only [hrem, ne_eq, not_true_eq_false, ↓reduceIte] at h
            rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session with ⟨res, s⟩
            rw [hdec] at h
            cases res with
            | error err => cases err <;> cases h
            | ok pt =>
              cases h
              exact Or.inl ⟨x, g, inner, out, s, rfl, rfl, hdec, rfl⟩
          · simp only [hrem, ne_eq, not_false_eq_true, ↓reduceIte] at h; cases h
        · simp only [hmat, ↓reduceIte] at h; cases h
      | none =>
        rw [hs] at h
        dsimp only at h
        cases hpk : preKeysNamedBy st m with
        | none => rw [hpk] at h; cases h
        | some k =>
          rw [hpk] at h
          dsimp only at h
          cases hrp : recvPrekeyState X W st.party st.me k m rc with
          | none => rw [hrp] at h; cases h
          | some opt =>
            rw [hrp] at h
            cases opt with
            | none => cases h
            | some xgpt =>
              rcases xgpt with ⟨x, g, pt⟩
              dsimp only at h
              cases hmk : markKyberUsed st m with
              | none => rw [hmk] at h; cases h
              | some st1 =>
                rw [hmk] at h
                cases h
                exact Or.inr ⟨k, x, g, out, st1, rfl, hrp, rfl, rfl⟩

private theorem removeOpk_kyberLastResort (st : PqParty) (m : PreKeyMessageFields) :
    (removeOpk st m).kyberLastResort = st.kyberLastResort := by
  unfold removeOpk
  cases m.opkId <;> rfl

/-- An accepted `PqStep` transition increases `lastResortUses` by at most `1` when
`st.kyberLastResort` has distinct pre-key IDs. -/
theorem pqStep_lastResortUses_le (X : UnreachedPqxdhPrimitives) (W : PEParams) (st st' : PqParty)
    (hnd : (st.kyberLastResort.map (·.1)).Nodup) (h : PqStep X W st st') :
    lastResortUses st' ≤ lastResortUses st + 1 := by
  cases h with
  | init b t st' out _ hmod =>
    rcases pqInitModel_eq_some_some X W st st' b t out hmod with ⟨_, _, _, rfl⟩
    unfold lastResortUses; dsimp only; omega
  | send m r st' out _ hmod =>
    rcases pqSendModel_eq_some_some W st st' m r.toList out hmod with ⟨_, _, _, _, _, _, _, rfl⟩
    unfold lastResortUses; dsimp only; omega
  | recvWhisper c rc st' out _ hmod =>
    rcases pqRecvWhisperModel_eq_some_some W st st' c rc out hmod with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    unfold lastResortUses; dsimp only; omega
  | recvPrekey m rc st' out _ _ hmod =>
    rcases pqRecvPrekeyModel_eq_some_some X W st st' m rc out hmod with
      ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, st1, _, _, hmk, rfl⟩
    · unfold lastResortUses; dsimp only; omega
    · unfold lastResortUses
      dsimp only
      rw [removeOpk_kyberLastResort]
      rcases markKyberUsed_eq_some st st1 m hmk with rfl | rfl
      · dsimp only; omega
      · exact map_lastResort_sum_le st.kyberLastResort m.kpkId (m.spkId, m.baseKey) hnd

/-- Pre-key promotion preserves `ReachablePqxdhSession`: if `.preKey` decryption succeeds on a
reachable session of encoded length `< 2^31`, the resulting session matches a reachable state. -/
theorem reachPq_promote (W : PEParams) (me : LocalIdentity) (x : RecordExtras) (g : GhostState Bytes)
    (c : List (BitVec 8)) (msg : SignalMessage) (rc : BitVec 256) (pt : List (BitVec 8))
    (s : SessionState Bytes)
    (hR : ReachablePqxdhSession W me x g) (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31)
    (hc : SignalMessage.tryFrom protoSignalCodec c = .ok msg)
    (hd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g.party)
      msg .preKey rc g.session = (.ok pt, s)) :
    ∃ g₁ : GhostState Bytes, ReachablePqxdhSession W me x g₁ ∧ g₁.party = g.party ∧ g₁.session = s :=
  Closure.Promote.reachPq_promote_proof W me x g c msg rc pt s hR hlen hc hd

private theorem initiateState_party (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party)
    (me : LocalIdentity) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (x : RecordExtras) (g : GhostState Bytes)
    (h : initiateState X W P me b t = some (x, g)) : g.party = P := by
  unfold initiateState at h
  cases hk : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
  | none => rw [hk] at h; cases h
  | some p =>
    rw [hk] at h
    rcases p with ⟨dk, hdr⟩
    dsimp only at h
    cases his : initializeInitiatorSession W.C (pqxdhSpqrSession W)
        ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
        (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) (HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | error _ => rw [his] at h; cases h
    | ok st_s => rw [his] at h; cases h; rfl

private theorem recvPrekeyState_party (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256)
    (x : RecordExtras) (g : GhostState Bytes) (pt : Bytes)
    (h : recvPrekeyState X W P me k m rc = some (some (x, g, pt))) : g.party = P := by
  unfold recvPrekeyState at h
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at h; cases h
  | ok inner =>
    rw [htry] at h
    dsimp only at h
    by_cases hid : m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId
    · simp only [hid, ↓reduceIte] at h; cases h
    · simp only [hid, ↓reduceIte] at h
      cases hak : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
      | none => rw [hak] at h; cases h
      | some dk =>
        rw [hak] at h
        dsimp only at h
        rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc
            (initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C me.idPriv).publicKey⟩
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))) with ⟨r, st_s⟩
        rw [hdec] at h
        cases r with
        | ok _ => cases h; rfl
        | error err => cases err <;> cases h

private theorem baseKeysBytes_length
    (seen : List (BitVec 32 × List.Vector (BitVec 8) 32)) :
    (baseKeysBytes seen).length = 37 * seen.length := by
  unfold baseKeysBytes
  induction seen with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨s, b⟩
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, ih]
    have hb : (djbKey b).length = 33 := by
      simp [djbKey, List.Vector.toList_length]
    have hle : (le32 s).length = 4 := by rfl
    omega

private theorem mem_seen_length_le
    (l : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)))
    (i : BitVec 32) (k : PqKyberKey)
    (seen : List (BitVec 32 × List.Vector (BitVec 8) 32))
    (hmem : (i, k, seen) ∈ l) :
    seen.length ≤ (l.map fun e => e.2.2.length).sum := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [List.mem_cons, List.map_cons, List.sum_cons] at hmem ⊢
    rcases hmem with rfl | htl
    · dsimp only
      omega
    · have h := ih htl
      omega

private theorem identityKey_serialize_length (k : IdentityKey) :
    k.serialize.length = 33 := by
  simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]

private theorem encodeDir_length_lt_of_rel (W : PEParams) (st st' : PqParty)
    (hparty : st'.party = st.party) (hme : st'.me = st.me) (hsigned : st'.signed = st.signed)
    (hot : ∀ p ∈ st'.oneTime, p ∈ st.oneTime ∨ p.2 = none)
    (hkot : ∀ p ∈ st'.kyberOneTime, p ∈ st.kyberOneTime ∨ p.2 = none)
    (hklr : ∀ e ∈ st'.kyberLastResort, ∃ seen₀, (e.1, e.2.1, seen₀) ∈ st.kyberLastResort)
    (hdir : ∀ f ∈ encodeDir W st, f.2.length < 2 ^ 31 ∧
      ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes))
    (hlr : lastResortUses st' < 2 ^ 25)
    (hrec : ∀ x g, st'.session = some (x, g) → (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes) :
    ∀ f ∈ encodeDir W st', f.2.length < 2 ^ 31 ∧
      ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes) := by
  intro f hf
  unfold encodeDir at hf
  rw [hparty, hme, hsigned] at hf
  simp only [List.mem_append] at hf
  rcases hf with ((((((hf3 | hfpeer) | hfsess) | hfsig) | hfot) | hfkot) | hfklr)
  · apply hdir f
    unfold encodeDir
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hf3)))))
  · cases hp : st'.peerId with
    | none => rw [hp] at hfpeer; cases hfpeer
    | some k =>
      rw [hp] at hfpeer
      simp only [List.mem_singleton] at hfpeer
      subst hfpeer
      simp only [identityKey_serialize_length]
      unfold fileCapBytes
      exact ⟨by omega, fun _ => by omega⟩
  · cases hs : st'.session with
    | none => rw [hs] at hfsess; cases hfsess
    | some xg =>
      rw [hs] at hfsess
      rcases xg with ⟨x, g⟩
      simp only [List.mem_singleton] at hfsess
      subst hfsess
      dsimp only
      have hle := hrec x g hs
      refine ⟨by unfold fileCapBytes at hle; omega, fun _ => hle⟩
  · apply hdir f
    unfold encodeDir
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hfsig)))
  · rcases List.mem_map.mp hfot with ⟨⟨i, k⟩, hmem, rfl⟩
    rcases hot (i, k) hmem with hmem₀ | hk0
    · apply hdir
      unfold encodeDir
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨(i, k), hmem₀, rfl⟩)))
    · dsimp only at hk0
      subst hk0
      simp [fileCapBytes]
  · rcases List.mem_map.mp hfkot with ⟨⟨i, k⟩, hmem, rfl⟩
    rcases hkot (i, k) hmem with hmem₀ | hk0
    · apply hdir
      unfold encodeDir
      simp only [List.mem_append]
      exact Or.inl (Or.inr (List.mem_map.mpr ⟨(i, k), hmem₀, rfl⟩))
    · dsimp only at hk0
      subst hk0
      simp [fileCapBytes]
  · rcases List.mem_flatten.mp hfklr with ⟨sub, hsub, hfsub⟩
    rcases List.mem_map.mp hsub with ⟨⟨i, k, seen'⟩, hmem, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfsub
    rcases hfsub with rfl | rfl
    · rcases hklr (i, k, seen') hmem with ⟨seen₀, hmem₀⟩
      apply hdir
      unfold encodeDir
      simp only [List.mem_append]
      refine Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨(i, k, seen₀), hmem₀, rfl⟩, ?_⟩)
      simp
    · dsimp only
      refine ⟨?_, fun hne => absurd rfl (hne i)⟩
      rw [baseKeysBytes_length]
      have hle := mem_seen_length_le st'.kyberLastResort i k seen' hmem
      unfold lastResortUses at hlr
      omega

private theorem map_fst_clear_opt {α β : Type} [DecidableEq α] (l : List (α × Option β)) (j : α) :
    (l.map (fun (i, k) => if i = j then (i, none) else (i, k))).map (·.1) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, k⟩
    simp only [List.map_cons, ih]
    split <;> rfl

private theorem map_fst_append_seen
    (l : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32)))
    (j : BitVec 32) (pair : BitVec 32 × List.Vector (BitVec 8) 32) :
    (l.map (fun (i, k, s) => if i = j then (i, k, s ++ [pair]) else (i, k, s))).map (·.1) =
      l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨i, k, s⟩
    simp only [List.map_cons, ih]
    split <;> rfl

/-- `PqxdhPartyInSpecDomain W` is closed under accepted `PqStep` transitions whenever
`lastResortUses st' < 2 ^ 25` and any stored session encodes to at most `fileCapBytes` bytes. -/
theorem wfPq_step (X : UnreachedPqxdhPrimitives) (W : PEParams) (st st' : PqParty) (hwf : PqxdhPartyInSpecDomain W st)
    (h : PqStep X W st st') (hlr : lastResortUses st' < 2 ^ 25)
    (hrec : ∀ x g, st'.session = some (x, g) → (encodeRecordUnderExtras (fun _ => x) g).length ≤ fileCapBytes) :
    PqxdhPartyInSpecDomain W st' := by
  rcases hwf with ⟨hsess_wf, hdir_wf, hnd_sig, hnd_ot, hnd_kot, hnd_klr⟩
  have hrec_lt : ∀ x g, st'.session = some (x, g) →
      (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := fun x g hs => by
    have hle := hrec x g hs; unfold fileCapBytes at hle; omega
  cases h with
  | init b t st' out _ hmod =>
    rcases pqInitModel_eq_some_some X W st st' b t out hmod with ⟨x, g, hinit, rfl⟩
    refine ⟨?_, ?_, hnd_sig, hnd_ot, hnd_kot, hnd_klr⟩
    · intro x' g' hs'
      dsimp only at hs'
      cases hs'
      exact ⟨⟨g, ReachablePqxdhSession.initiate X st.party st.me b t x g hinit, rfl, rfl⟩,
        initiateState_party X W st.party st.me b t x g hinit,
        hrec_lt x g rfl⟩
    · exact encodeDir_length_lt_of_rel W st _ rfl rfl rfl
        (fun _ hp => Or.inl hp) (fun _ hp => Or.inl hp) (fun e he => ⟨e.2.2, he⟩)
        hdir_wf hlr hrec
  | send m r st' out _ hmod =>
    rcases pqSendModel_eq_some_some W st st' m r.toList out hmod with
      ⟨x, g, msg, s, k, hs_old, henc, rfl⟩
    rcases hsess_wf x g hs_old with ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hp_old, hlen_old⟩
    refine ⟨?_, ?_, hnd_sig, hnd_ot, hnd_kot, hnd_klr⟩
    · intro x' g' hs'
      dsimp only at hs'
      cases hs'
      have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
        unfold encodeRecordUnderExtras at hlen_old ⊢
        rw [hs₀]
        exact hlen_old
      have henc₀ : SessionState.messageEncrypt (pqxdhSessionParams W).C
          (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).sendAddrs g₀.party) m r.toList g₀.session = (.ok msg, s) := by
        rw [hp₀, hs₀]
        exact henc
      let g₁ := ((pqxdhSessionParams W).send g₀ m r.toList).1
      have hg₁ : g₁.party = g₀.party ∧ g₁.session = s := by
        show ((pqxdhSessionParams W).send g₀ m r.toList).1.party = _ ∧
          ((pqxdhSessionParams W).send g₀ m r.toList).1.session = _
        unfold Params.send
        rw [henc₀]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨g₁, ReachablePqxdhSession.send m r.toList hR₀ hlen₀, hg₁.1.trans hp₀, hg₁.2⟩, hp_old, hrec_lt x _ rfl⟩
    · exact encodeDir_length_lt_of_rel W st _ rfl rfl rfl
        (fun _ hp => Or.inl hp) (fun _ hp => Or.inl hp) (fun e he => ⟨e.2.2, he⟩)
        hdir_wf hlr hrec
  | recvWhisper c rc st' out _ hmod =>
    rcases pqRecvWhisperModel_eq_some_some W st st' c rc out hmod with
      ⟨x, g, msg, pt, s, k, hs_old, hc, hd, rfl⟩
    rcases hsess_wf x g hs_old with ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hp_old, hlen_old⟩
    refine ⟨?_, ?_, hnd_sig, hnd_ot, hnd_kot, hnd_klr⟩
    · intro x' g' hs'
      dsimp only at hs'
      cases hs'
      have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
        unfold encodeRecordUnderExtras at hlen_old ⊢
        rw [hs₀]
        exact hlen_old
      have hd₀ : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).expectedAddrs g₀.party) msg .whisper rc g₀.session = (.ok pt, s) := by
        rw [hp₀, hs₀]
        exact hd
      let idx := g₀.session.receiverChains.findIdx? (·.senderRatchetKey == msg.senderRatchetKey)
      let trip := match idx with
        | some i => (g₀.chainEpochs.getD i 0, g₀.chainEpochs, g₀.epoch)
        | none => (g₀.epoch + 1, g₀.chainEpochs ++ [g₀.epoch + 1], g₀.epoch + 1)
      let epochs := trip.2.1.drop (trip.2.1.length - s.receiverChains.length)
      let g₁ : GhostState Bytes := { g₀ with session := s, epoch := trip.2.2, chainEpochs := epochs }
      have hcodec : (pqxdhSessionParams W).codec = protoSignalCodec := rfl
      have hC : (pqxdhSessionParams W).C = W.C := rfl
      have hspqr : (pqxdhSessionParams W).spqr = pqxdhSpqrSession W := rfl
      have hrecv : (pqxdhSessionParams W).receive g₀ c rc =
          some (g₁, trip.1, msg.counter.toNat + 1, pt) := by
        unfold Params.receive
        rw [hcodec, hc]
        dsimp only
        rw [hC, hspqr, hd₀]
        rfl
      exact ⟨⟨g₁, ReachablePqxdhSession.recv hR₀ hlen₀ hrecv, hp₀, rfl⟩, hp_old, hrec_lt x _ rfl⟩
    · exact encodeDir_length_lt_of_rel W st _ rfl rfl rfl
        (fun _ hp => Or.inl hp) (fun _ hp => Or.inl hp) (fun e he => ⟨e.2.2, he⟩)
        hdir_wf hlr hrec
  | recvPrekey m rc st' out _ _ hmod =>
    rcases pqRecvPrekeyModel_eq_some_some X W st st' m rc out hmod with
      ⟨x, g, inner, pt, s, hs_old, htry, hd, rfl⟩ |
      ⟨k, x, g, pt, st1, _, hrp, hmk, rfl⟩
    · rcases hsess_wf x g hs_old with ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hp_old, hlen_old⟩
      refine ⟨?_, ?_, hnd_sig, hnd_ot, hnd_kot, hnd_klr⟩
      · intro x' g' hs'
        dsimp only at hs'
        cases hs'
        have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
          unfold encodeRecordUnderExtras at hlen_old ⊢
          rw [hs₀]
          exact hlen_old
        have hd₀ : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
            ((pqxdhSessionParams W).expectedAddrs g₀.party) inner .preKey rc g₀.session = (.ok pt, s) := by
          rw [hp₀, hs₀]
          exact hd
        rcases reachPq_promote W st.me x g₀ m.inner inner rc pt s hR₀ hlen₀ htry hd₀ with
          ⟨g₁, hR₁, hp₁, hs₁⟩
        exact ⟨⟨g₁, hR₁, hp₁.trans hp₀, hs₁⟩, hp_old, hrec_lt x _ rfl⟩
      · exact encodeDir_length_lt_of_rel W st _ rfl rfl rfl
          (fun _ hp => Or.inl hp) (fun _ hp => Or.inl hp) (fun e he => ⟨e.2.2, he⟩)
          hdir_wf hlr hrec
    · have hrop_party : (removeOpk st1 m).party = st1.party := by unfold removeOpk; cases m.opkId <;> rfl
      have hrop_me : (removeOpk st1 m).me = st1.me := by unfold removeOpk; cases m.opkId <;> rfl
      have hrop_sig : (removeOpk st1 m).signed = st1.signed := by unfold removeOpk; cases m.opkId <;> rfl
      have hrop_kot : (removeOpk st1 m).kyberOneTime = st1.kyberOneTime := by
        unfold removeOpk; cases m.opkId <;> rfl
      have hrop_klr : (removeOpk st1 m).kyberLastResort = st1.kyberLastResort :=
        removeOpk_kyberLastResort st1 m
      have hrop_ot_nd : ((removeOpk st1 m).oneTime.map (·.1)).Nodup ↔
          (st1.oneTime.map (·.1)).Nodup := by
        unfold removeOpk
        cases m.opkId with
        | none => rfl
        | some j => dsimp only; rw [map_fst_clear_opt]
      have hrop_ot_mem : ∀ p ∈ (removeOpk st1 m).oneTime, p ∈ st1.oneTime ∨ p.2 = none := by
        intro p hp
        unfold removeOpk at hp
        cases hopk : m.opkId with
        | none => rw [hopk] at hp; exact Or.inl hp
        | some j =>
          rw [hopk] at hp
          dsimp only at hp
          rcases List.mem_map.mp hp with ⟨⟨i, opt⟩, hmem, heq⟩
          by_cases hij : i = j
          · simp only [hij, ↓reduceIte] at heq; subst heq; exact Or.inr rfl
          · simp only [hij, ↓reduceIte] at heq; subst heq; exact Or.inl hmem
      rcases markKyberUsed_eq_some st st1 m hmk with rfl | rfl
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x' g' hs'
          dsimp only at hs'
          cases hs'
          dsimp only
          rw [hrop_me, hrop_party]
          exact ⟨⟨g, ReachablePqxdhSession.recvPrekey X st.party st.me k m rc x g pt hrp, rfl, rfl⟩,
            recvPrekeyState_party X W st.party st.me k m rc x g pt hrp,
            hrec_lt x g rfl⟩
        · refine encodeDir_length_lt_of_rel W st _ hrop_party hrop_me hrop_sig hrop_ot_mem ?_ ?_
            hdir_wf hlr hrec
          · intro p hp
            dsimp only at hp
            rw [hrop_kot] at hp
            rcases List.mem_map.mp hp with ⟨⟨i, opt⟩, hmem, heq⟩
            by_cases hij : i = m.kpkId
            · simp only [hij, ↓reduceIte] at heq; subst heq; exact Or.inr rfl
            · simp only [hij, ↓reduceIte] at heq; subst heq; exact Or.inl hmem
          · intro e he
            dsimp only at he
            rw [hrop_klr] at he
            exact ⟨e.2.2, he⟩
        · dsimp only; rw [hrop_sig]; exact hnd_sig
        · dsimp only; exact hrop_ot_nd.mpr hnd_ot
        · dsimp only; rw [hrop_kot]; dsimp only; rw [map_fst_clear_opt]; exact hnd_kot
        · dsimp only; rw [hrop_klr]; exact hnd_klr
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x' g' hs'
          dsimp only at hs'
          cases hs'
          dsimp only
          rw [hrop_me, hrop_party]
          exact ⟨⟨g, ReachablePqxdhSession.recvPrekey X st.party st.me k m rc x g pt hrp, rfl, rfl⟩,
            recvPrekeyState_party X W st.party st.me k m rc x g pt hrp,
            hrec_lt x g rfl⟩
        · refine encodeDir_length_lt_of_rel W st _ hrop_party hrop_me hrop_sig hrop_ot_mem ?_ ?_
            hdir_wf hlr hrec
          · intro p hp
            dsimp only at hp
            rw [hrop_kot] at hp
            exact Or.inl hp
          · intro e he
            dsimp only at he
            rw [hrop_klr] at he
            dsimp only at he
            rcases List.mem_map.mp he with ⟨⟨i, kk, s₀⟩, hmem, heq⟩
            by_cases hij : i = m.kpkId
            · subst hij; simp only [↓reduceIte] at heq; subst heq; exact ⟨s₀, hmem⟩
            · simp only [hij, ↓reduceIte] at heq; subst heq; exact ⟨s₀, hmem⟩
        · dsimp only; rw [hrop_sig]; exact hnd_sig
        · dsimp only; exact hrop_ot_nd.mpr hnd_ot
        · dsimp only; rw [hrop_kot]; exact hnd_kot
        · dsimp only; rw [hrop_klr]; dsimp only; rw [map_fst_append_seen]; exact hnd_klr

end CryptoVerification.SignalSession
