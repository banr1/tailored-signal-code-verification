/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3BinaryOomSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Model
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.Ok
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk

/-!
# Pure Store & Message Rejection Predicates and `decPkDef` Helpers (`pkToE? pm = none`)

Pure `scopeIn` injectivity/coverage lemmas, store and message rejection predicates
(`DecPkStoreOk`, `MsgCondPkToENone`, `DecPkOkD3Untyped`), and `decPkDef` evaluation to
`some none` when `pkToE? pm = none` and no active session matches `pm`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3

open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification.E2E (
  PEParams RecordExtras UnreachedPqxdhPrimitives wirePrekey
)
open CryptoVerification.E2E.Record (toRecord)
open CryptoVerification.E2E.RecordX (
  extrasOf sessionOfX sessionOfX_wf toRecord_extrasOf_eq
)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.SignalSession (
  PqParty PqxdhPartyInSpecDomain pqRecvInputs
)
open CryptoVerification.SignalSession.Cli (StoresGhost baseKeysName utf8)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (SlotAns runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (
  PreKeyFilesWf SameServiceId SessMatchesPm decPkDef pkToE?
)
open CryptoVerification.SignalSession.Cli.RunProofs.DecPkS0 (
  baseKeysLt_pqRecv keyPairLt_pqRecv kyberLastResortWf_pqRecv kyberOneTimeWf_pqRecv
  loadRec_pqRecv_eq oneTimeWf_pqRecv signedWf_pqRecv
)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunRefine (addrValE)
open CryptoVerification.SignalSession.Cli.Slots (
  EncodeInjOn encodeInjOn_deserializeScopeP_Q loadRec not_sameServiceId_party scopeIn
  scopeKit_of_scopeIn
)
open CryptoVerification.SignalSession.Cli.Slots.PqValid (
  pqRatchetState_length_le_encodeRecordX reachPq_inv reachPq_validState
)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (d3PqSessionOf)

theorem encodeInjOn_scopeIn : EncodeInjOn scopeIn :=
  fun r₁ r₂ h₁ h₂ henc =>
    encodeInjOn_deserializeScopeP_Q r₁ r₂
      (scopeKit_of_scopeIn h₁) (scopeKit_of_scopeIn h₂) henc

theorem ratchetScopeCoversPq_scopeIn (W : PEParams) :
    ∀ st x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
      scopeIn (toRecord (extrasOf fun _ => x) g) := by
  intro st x g hwf hs
  have hwf_sess := hwf.1 x g hs
  rcases hwf_sess.1 with ⟨g₀, hr, _, hsess₀⟩
  have hlen31 := hwf_sess.2.2
  have hval : CryptoVerification.SpqrV1.Top.StateSize.ValidState g.session.pqRatchetState :=
    hsess₀ ▸ reachPq_validState hr
  have hpq31 : g.session.pqRatchetState.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (pqRatchetState_length_le_encodeRecordX (fun _ => x) g) hlen31
  obtain ⟨hseeds₀, hrc₀, _, _, hrepr₀, _, hts, _, habk, hky⟩ := reachPq_inv hr
  rw [hsess₀] at hseeds₀ hrc₀ hrepr₀
  rw [toRecord_extrasOf_eq]
  refine ⟨⟨?_, ?_, ?_⟩, sessionOfX (fun _ => x) g, rfl, ?_⟩
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hseeds₀, Nat.lt_of_le_of_lt hrc₀ (by decide), fun k hk' => ?_⟩
    unfold sessionOfX at hk'; dsimp only at hk'
    split at hk'; · rw [hky k hk']; decide
    · cases hk'
  · intro s hs'; injection hs' with hs'; subst hs'; exact ⟨hval, hpq31⟩
  · intro s hs'; injection hs' with hs'; subst hs'
    refine ⟨hrepr₀.1, hrepr₀.2, sessionOfX_wf (fun _ => x) g, ?_⟩
    show x.aliceBaseKey.length < 2 ^ 32; rw [habk]; decide
  · refine ⟨hrc₀, ?_, ?_, Or.inr habk⟩
    · intro p hp; unfold sessionOfX at hp; dsimp only at hp
      split at hp; · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · intro k hk'; unfold sessionOfX at hk'; dsimp only at hk'
      split at hk'; · exact hky k hk'
      · cases hk'

/-- Message- and scope-independent store well-formedness predicate (dropping `typed` and
`sessMatch` from `DecPkOk₀`). -/
structure DecPkStoreOk (W : PEParams) (F : FsFiles) : Prop where
  keyPairLt : ∀ bs,
    StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
    bs.length < 2 ^ 32
  preKeysWf : PreKeyFilesWf W F
  baseKeysLt : ∀ i bs,
    StoresGhost.opened.kyber.lastResort.get cliIo.rd F (baseKeysName i) = .ok bs →
    bs.length < 2 ^ 32

/-- Message rejection condition: `pm` parses from some wire body via `pksmParse`,
has `pkToE? pm = none`, has distinct peer/self service IDs, and matches no active session. -/
def MsgCondPkToENone (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  (∃ body : List (BitVec 8), pksmParse body = some pm) ∧
  pkToE? pm = none ∧
  ¬ SameServiceId peer me ∧
  ∀ r s, loadRec Scope F peer = .ok (some r) →
    r.currentSession = some s → ¬ SessMatchesPm s pm

/-- `decPkOk` predicate combining `DecPkStoreOk` and `MsgCondPkToENone`. -/
def DecPkOkD3Untyped (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  DecPkStoreOk W F ∧ MsgCondPkToENone Scope F peer me pm

/-- Whenever `pkToE? pm = none` and no loaded active session matches `pm`, `decPkDef`
evaluates to `some none`. -/
theorem decPkDef_eq_some_none_of_d3b3
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) (coins : List (BitVec 8))
    (hpk : pkToE? pm = none)
    (hnoMatch : ∀ r s, loadRec Scope F peer = .ok (some r) →
      r.currentSession = some s → ¬ SessMatchesPm s pm) :
    decPkDef X W Scope F peer me pm coins = (some none : SlotAns (List (BitVec 8))) := by
  unfold decPkDef
  dsimp only
  cases hload : loadRec Scope F peer with
  | error _ => rfl
  | ok opt =>
    dsimp only
    cases StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey with
    | error _ => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        dsimp only
        cases opt with
        | none =>
          dsimp only [Option.bind]
          rw [hpk]
        | some r =>
          dsimp only [Option.bind]
          cases hcur : r.currentSession with
          | none => rw [hpk]
          | some s =>
            have hnm := hnoMatch r s hload hcur
            simp only [hnm, ↓reduceIte]

theorem toRecord_currentSession_eq_d3PqSessionOf (x : RecordExtras)
    (g : GhostState (List (BitVec 8))) :
    (toRecord (extrasOf fun _ => x) g).currentSession = some (d3PqSessionOf x g) :=
  rfl

/-- `DecPkStoreOk` holds on `runFiles (pqRecvInputs W st c rc)` for any well-formed `st`. -/
theorem decPkStoreOk_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) :
    DecPkStoreOk W (runFiles (pqRecvInputs W st c rc)) where
  keyPairLt := keyPairLt_pqRecv W st c rc hwf
  preKeysWf :=
    ⟨signedWf_pqRecv W st c rc,
     oneTimeWf_pqRecv W st c rc,
     kyberOneTimeWf_pqRecv W st c rc,
     kyberLastResortWf_pqRecv W st c rc⟩
  baseKeysLt := baseKeysLt_pqRecv W st c rc hwf

/-- Loaded peer session records on `pqRecvInputs W st c rc` never match `pm` when `hnomatch` holds. -/
theorem not_sessMatchesPm_pqRecv (W : PEParams) (st : PqParty) (c : List (BitVec 8))
    (pm : PreKeySignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    ∀ r s, loadRec scopeIn (runFiles (pqRecvInputs W st c rc))
        (addrValE st.party.other) = .ok (some r) →
      r.currentSession = some s → ¬ SessMatchesPm s pm := by
  intro r s hload hcur
  rw [loadRec_pqRecv_eq encodeInjOn_scopeIn (ratchetScopeCoversPq_scopeIn W) st c rc hwf]
    at hload
  cases hsess : st.session with
  | none => rw [hsess] at hload; cases hload
  | some xg =>
    obtain ⟨x, g⟩ := xg
    rw [hsess] at hload
    injection hload with hr; injection hr with hr; subst hr
    rw [toRecord_currentSession_eq_d3PqSessionOf] at hcur
    injection hcur with hs; subst hs
    exact hnomatch x g hsess

/-- `MsgCondPkToENone` holds on `pqRecvInputs W st (wirePrekey :: body) rc` when
`pksmParse body = some pm`, `pkToE? pm = none`, and no active session matches `pm`. -/
theorem msgCondPkToENone_pqRecv (W : PEParams) (st : PqParty) (body : List (BitVec 8))
    (pm : PreKeySignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : pksmParse body = some pm)
    (huntyped : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    MsgCondPkToENone scopeIn (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (addrValE st.party.other) (addrValE st.party) pm :=
  ⟨⟨body, hparse⟩, huntyped, not_sameServiceId_party st.party,
    not_sessMatchesPm_pqRecv W st (wirePrekey :: body) pm rc hwf hnomatch⟩

theorem decPkOkD3Untyped_pqRecv (W : PEParams) (st : PqParty) (body : List (BitVec 8))
    (pm : PreKeySignalMessage) (rc : BitVec 256) (hwf : PqxdhPartyInSpecDomain W st)
    (hparse : pksmParse body = some pm)
    (huntyped : pkToE? pm = none)
    (hnomatch : ∀ x g, st.session = some (x, g) → ¬ SessMatchesPm (d3PqSessionOf x g) pm) :
    DecPkOkD3Untyped W scopeIn (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (addrValE st.party.other) (addrValE st.party) pm :=
  ⟨decPkStoreOk_pqRecv W st (wirePrekey :: body) rc hwf,
    msgCondPkToENone_pqRecv W st body pm rc hwf hparse huntyped hnomatch⟩

end LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3PollRejectAuxF3
