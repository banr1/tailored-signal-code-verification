/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecord.DRBound
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import LibsignalBinary.Proofs.SignalSession.Closure.Promote

/-!
# Promote Pre-Key Receive Model and Session Closure

Proves `ReachablePqxdhSession` and `WireRecCanon` closure under matching-session promote pre-key
`recv` steps, and defines `BobPromDirInv`, `PromPureAcceptOut`, and `rpkPromMid`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW interpW)
open Symbolic.Swarm.CREF.CliPure (PureDecryptCoinsOk)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pureCoinsOf pinCoins)
open Symbolic.Swarm.CREF.TR.Pure (PureRecordRepr slots_SessionScopeP slots_RecordInScopeP slots_NonEmptyV1Q slots_RecordScopeP slots_DeserializeScopeP_Q slots_RecordCanonical_Q WireRecCanon)

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set
  mut_exec_modify mut_exec_modifyGet mut_exec_liftE mut_exec_bind mut_exec_onRatchet

/-! ## Decrypt Success Inversion -/

theorem rpkProm_tryDecryptWithStateW_pendingPreKey_false {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W_aes : AesW} {spqr : Spqr PQ PQC}
    {expected : Option HwBytes} {msg : SignalMessage} {ty : MessageType} {coins : BitVec 256}
    {st s : SessionState PQ} {pt : HwBytes}
    (h : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
      expected msg ty coins) st = (.ok pt, s)) :
    s.pendingPreKey = false := by
  unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW at h
  simp only [mut_exec_bind] at h
  rcases hfrom : Mut.exec (TripleRatchet.fromSessionState (PQ := PQ)) st with ⟨e | tr0, taken⟩
  · rw [hfrom] at h; cases h
  · rw [hfrom] at h; dsimp only at h
    rcases hdec : Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W_aes spqr
        expected msg ty coins) tr0 with ⟨e | pt', tr'⟩
    · simp [hdec] at h
    · simp only [hdec, mut_exec_liftE, mut_exec_modify, mut_exec_pure,
        Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      rfl

theorem rpkProm_tryDecryptFromRecordW_ok_inv {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {W_aes : AesW} {spqr : Spqr PQ PQC}
    {expected : Option HwBytes} {msg : SignalMessage} {ty : MessageType} {coins : BitVec 256}
    {st s : SessionState PQ} {pt : HwBytes}
    (h : Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr
      expected msg ty coins st = (.ok pt, s)) :
    st.version.toNat = msg.messageVersion.toNat ∧
    Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
      expected msg ty coins) st = (.ok pt, s) ∧
    s.pendingPreKey = false := by
  unfold Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW at h
  split_ifs at h with hv
  · cases h
  · rcases hex : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
        expected msg ty coins) st with ⟨e | ptext, updated⟩
    · rw [hex] at h; cases h
    · rw [hex] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, rfl, rpkProm_tryDecryptWithStateW_pendingPreKey_false hex⟩

/-! ## Promote Session Closure and Record Canonicality -/

theorem rpkProm_encodeRecordX_session_congr (x : RecordExtras) (g₀ g : GhostState HwBytes)
    (hs : g₀.session = g.session) :
    encodeRecordUnderExtras (fun _ => x) g₀ = encodeRecordUnderExtras (fun _ => x) g := by
  rw [encodeRecordX_eq_encodeRecord_pqSession, encodeRecordX_eq_encodeRecord_pqSession]
  apply congrArg (fun s => CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩)
  simp [pqSession, hs]

theorem rpkProm_reachPq_promote {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    {c : HwBytes} {inner : SignalMessage} {rc : BitVec 256}
    {pt : HwBytes} {s : SessionState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (htry : SignalMessage.tryFrom protoSignalCodec c = .ok inner)
    (hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g.party) inner .preKey rc g.session = (.ok pt, s)) :
    ∃ g₁ : GhostState HwBytes,
      ReachablePqxdhSession W st.me x g₁ ∧ g₁.party = g.party ∧ g₁.session = s := by
  obtain ⟨⟨g₀, hrpq₀, hp₀, hs₀⟩, _, hlen31⟩ := hwf.1 x g hsess
  have hlen31_g0 : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
    rwa [rpkProm_encodeRecordX_session_congr x g₀ g hs₀]
  have hdec_g0 : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
      ((pqxdhSessionParams W).expectedAddrs g₀.party) inner .preKey rc g₀.session = (.ok pt, s) := by
    rwa [hp₀, hs₀]
  obtain ⟨g₁, hrpq₁, hp₁, hs₁⟩ :=
    CryptoVerification.SignalSession.Closure.Promote.reachPq_promote_proof
      W st.me x g₀ c inner rc pt s hrpq₀ hlen31_g0 htry hdec_g0
  exact ⟨g₁, hrpq₁, hp₁.trans hp₀, hs₁⟩

theorem rpkProm_drCaps_of_reachPqInv {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g₁ : GhostState HwBytes}
    (hinv : ReachPqInvPure W me x g₁) :
    Symbolic.Swarm.TRREF.GrowthRecord.DRCaps (pqSession x g₁) := by
  obtain ⟨_, hseeds, hrcLe, _, _, hrep, _, _, _, _, _⟩ := hinv
  exact ⟨hrcLe, fun c hc => ⟨hrep.1 c hc, hseeds c hc⟩⟩

theorem rpkProm_wireRecCanon_of_reachPqInv {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g₁ : GhostState HwBytes}
    (hinv : ReachPqInvPure W me x g₁)
    (hppk : g₁.session.pendingPreKey = false)
    (hlen32 : (encodeRecordUnderExtras (fun _ => x) g₁).length < 2 ^ 32) :
    WireRecCanon (encodeRecordUnderExtras (fun _ => x) g₁) := by
  obtain ⟨_, hseeds, hrcLe, _, ⟨rem, hrem⟩, hrep, _, hts, _, habk, hkyb⟩ := hinv
  let sx := pqSession x g₁
  have hpqBound : slots_RecordScopeP slots_NonEmptyV1Q ⟨some sx⟩ :=
    recordScopeP_of_encodeRecordX_length x g₁ hlen32
  have hinScope : slots_RecordInScopeP ⟨some sx⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    refine ⟨hseeds, by dsimp [sx, pqSession]; unfold maxReceiverChains at hrcLe; omega, fun k hk => ?_⟩
    simp only [sx, pqSession_pendingKyberPreKey] at hk
    split at hk
    · have hklen := hkyb k hk; omega
    · cases hk
  have hrecRepr : PureRecordRepr ⟨some sx⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    refine ⟨hrep.1, hrep.2, ?_, ?_⟩
    · dsimp [Session.Wf, sx, pqSession]; cases g₁.session.pendingPreKey <;> rfl
    · simp only [sx, pqSession_aliceBaseKey]; omega
  have hsessScopeP : slots_SessionScopeP sx := by
    refine ⟨hrcLe, fun p hp => ?_, fun k hk => ?_, ?_⟩
    · simp only [sx, pqSession_pendingPreKey] at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · simp only [sx, pqSession_pendingKyberPreKey] at hk
      split at hk
      · exact hkyb k hk
      · cases hk
    · simp only [sx, pqSession_aliceBaseKey]; exact Or.inr habk
  have hdeser : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some sx⟩ :=
    ⟨⟨hinScope, hpqBound, hrecRepr⟩, sx, rfl, hsessScopeP⟩
  have henc := encodeRecordX_eq_encodeRecord_pqSession x g₁
  have hrcq : slots_RecordCanonical_Q slots_NonEmptyV1Q (encodeRecordUnderExtras (fun _ => x) g₁) sx :=
    ⟨henc, hdeser, pureBinCanonSession_of_deserializeScopeP_Q_any hdeser⟩
  have hrem_some : sx.state.remoteIdentity.isSome = true := by
    change g₁.session.remoteIdentity.isSome = true; rw [hrem]; rfl
  exact ⟨sx, hrcq, hinScope, hpqBound, hrem_some, by omega,
    pqSession_pendingPreKey_of_false x g₁ hppk⟩

/-! ## Directory Invariant and Promote Accept Witness -/

theorem rpkProm_pureCoinsOf_eq_bytesToKey32 {bs : HwBytes} (hlen : bs.length = 32) :
    pureCoinsOf bs = HKDF.bytesToKey32 bs := by
  unfold pureCoinsOf
  have h1 : (bs ++ List.replicate 32 0#8).take 32 = bs.take 32 :=
    List.take_append_of_le_length (by omega)
  have h2 : bs.take 32 = bs := List.take_of_length_le (by omega)
  rw [h1, h2]

theorem rpkProm_cliPureSpqrOf_eq (interp : ExternInterpretation) :
    pureSpqrOf interp = Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp := rfl

theorem rpkProm_cliDrawsCoins_eq {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey) :
    drawsCoins C st their = Symbolic.Swarm.CREF.CliPure.pureDrawsCoins C st their := rfl

/-- Directory-model invariant on Bob's `st : PqParty` for a matching-session promote `recv` call. -/
structure BobPromDirInv (interp : ExternInterpretation) (W : PEParams)
    (r : ProtocolSetup) (st : PqParty) (rec_ : HwBytes) : Prop where
  party  : st.party = .B
  peerId : ∃ kA : IdentityKey, st.peerId = some kA ∧
             kA.serialize = ecKey (pubBytes interp (secretBytes r 0))
  wfSt   : PqxdhPartyInSpecDomain W st
  sessEq : ∃ x g, st.session = some (x, g) ∧ rec_ = encodeRecordUnderExtras (fun _ => x) g

theorem rpkProm_sess_pendingKyberPreKey_none {W : PEParams} {r : ProtocolSetup}
    {records : Participant → Option HwBytes} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes} {rec_ : HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hrec_eq : rec_ = encodeRecordUnderExtras (fun _ => x) g)
    (hrec_bob : records r.bob = some rec_)
    (hbkn : Symbolic.Swarm.CREF.PureBobKyberNone r records) :
    (pqSession x g).pendingKyberPreKey = none := by
  let sx := pqSession x g
  have hlen31 : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 :=
    (reachPqInvPure_of_wfPq hwf hsess).2.2
  have henc_sx := encodeRecordX_eq_encodeRecord_pqSession x g
  have hlt63 : (CryptoVerification.E2E.Record.encodeRecord ⟨some sx⟩).length < 2 ^ 63 := by
    rw [← henc_sx]; omega
  have hrb := recordBytes_sessionToRecordRecPending_of_encodeRecord_lt sx hlt63
  have hrec_rb : records r.bob =
      some (DY.Libsignal.Composed.Refinement.recordBytes (sessionToRecordRecPending sx)) := by
    rw [hrec_bob, hrec_eq, henc_sx, ← hrb]
  have hnone := hbkn (sessionToRecordRecPending sx) hrec_rb
  simp only [sessionToRecordRecPending, Option.map_eq_none_iff] at hnone
  exact hnone

/-- Pure witness of the promote-accept model evaluation. -/
structure PromPureAcceptOut (interp : ExternInterpretation) (r : ProtocolSetup)
    (rec_ b rec' : HwBytes) (mid : List MachineEvent) (pt : HwBytes)
    (pf : PreKeyFields) (sess sess' : Session HwBytes)
    (coins : BitVec 256) (expected : Option HwBytes) : Prop where
  hpf        : parsePreKeyWire b = some pf
  hcan_in    : slots_RecordCanonical_Q slots_NonEmptyV1Q rec_ sess
  hcoins     : (coins = 0#256 ∧ mid = []) ∨
               (∃ rb : HwBytes, mid = [.rng rb] ∧ rb.length = 32 ∧
                 coins = pinCoins (some rb) ∧
                 Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (cryptoOf' interp) sess.state
                   pf.inner.senderRatchetKey = true)
  hdecOk     : PureDecryptCoinsOk (cryptoOf' interp) sess.state pf.inner.senderRatchetKey coins
  hexec      : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
                 (cryptoOf' interp) (interpW interp) (Symbolic.Swarm.CREF.CliPure.pureSpqrOf interp)
                 expected pf.inner .preKey coins) sess.state = (.ok pt, sess'.state)
  halice     : sess'.aliceBaseKey = sess.aliceBaseKey
  hpend      : sess'.pendingPreKey = none
  hkyb       : sess'.pendingKyberPreKey = sess.pendingKyberPreKey
  hstate     : rec' = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩
  hlen_out   : rec'.length < 2 ^ 32
  hwrc       : WireRecCanon rec'
  hooo_out   : Symbolic.Swarm.CREF.SpqrOooBounded (Symbolic.Swarm.CREF.pqStateOf rec')
  hcanon_out : rec'.length < 2 ^ 32 - 2 ^ 20 → Symbolic.Swarm.CREF.TR.PureTRRecordCanon r r.bob rec'
  hver       : pf.inner.messageVersion = 4#8
  hnodraw    : mid = [] → Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (cryptoOf' interp) sess.state
                 pf.inner.senderRatchetKey = false

/-- Deterministic `(who, ok)`-independent middle event list of a promote accept call. -/
def rpkPromMid (interp : ExternInterpretation) (x : RecordExtras) (g : GhostState HwBytes)
    (inner : SignalMessage) (c_coins : HwBytes) : List MachineEvent :=
  if Symbolic.Swarm.CREF.CliPure.pureDrawsCoins (cryptoOf' interp) (pqSession x g).state
      inner.senderRatchetKey then
    [.rng c_coins]
  else
    []

end Symbolic.Swarm.CREF.Cli
