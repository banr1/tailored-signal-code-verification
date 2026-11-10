/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.CBad
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PkDispatchAtPure
public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.RecvFresh
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvWire.By2SupplyA
import Symbolic.Proofs.Swarm.CREF.TR.ByteChainReselect.C16
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepSkippedProvTR
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Whisper Receive Supply Predicates and Dischargers

Defines `SkippedPkDispatchAtKPure`, `RcvByteChainReselectAt`, and `RcvSkippedNotJunkSeedProvAt`,
and discharges byte-chain reselection, non-junk skipped-key provenance, and `NoRatchetPkDispatchAtSt`
from `CleanBy`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv
open _root_.Symbolic.Swarm.CREF.TR _root_.Symbolic.Swarm.CREF.CliPure.TR

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain recvChainFor consumeMessageKey computeMac hmac
  trHonestWireMsg messageVersion)
open DY.Libsignal.Refinement (ExternCryptoLawsHold aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open DY.Libsignal.TripleRatchet
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk (SkippedVarConcl)

/-- Skipped-key public-key dispatch supply predicate. -/
def SkippedPkDispatchAtKPure
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx₀ : Nat) (body ptBytes : HwBytes) (m : SignalMessage) (st₀ st_prov : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat),
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body →
    parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion →
    msg₀.counter = UInt32.ofBitVec m.counter →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ¬ReselectCollision interpretation r₀ S g ms₁ t₀ →
    ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀ →
    st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) →
    (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) →
    (∀ (msg : TRSignalMsg), msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter →
      recvSeed st_prov msg = some seed) →
    k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st_prov msg₀ →
    k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack →
    (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx →
    TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ →
    TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) →
    (TR.G1.JunkTR pk → ∀ x, pk.view? DY.X25519.Variant.SubF = some x → seed.AttackerKnows (runTraceMoves r₀ ms₁)) →
    gamma interpretation S g pk = m.senderRatchetKey.bytes.toList →
    body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) →
    st_prov.peerIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    st_prov.myIk.AttackerKnows (runTraceMoves r₀ ms₁) →
    interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes →
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧ parseTrSignalMsg t₁ = some msg₁ ∧
      msg₁.version = messageVersion ∧ msg₁.ratchetKey = pk ∧ msg₁.counter = msg₀.counter ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
      (seed.AttackerKnows (runTraceMoves r₀ ms₁) ∨ ∃ salt ∈ honestSalts r₀ ms₁,
        AuthenticDecryptRepB3AtSt interpretation r₀ S g ms₁ body ptBytes t₁ msg₁ st_prov salt seed ∧
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) =
          gamma interpretation S g (computeMac (trMsgKeys salt seed).macKey st_prov.peerIk st_prov.myIk msg₁.wire) ∧
        interpretation aesCbcDecryptSymbol
          [m.ciphertext, gamma interpretation S g (trMsgKeys salt seed).cipherKey,
           (gamma interpretation S g (trMsgKeys salt seed).iv).take 16] = some ptBytes)

/-- Byte-chain reselection obligation at `(r₀, S, g, ms₁, τ₁)`. -/
def RcvByteChainReselectAt
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (body : HwBytes) (m : SignalMessage) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (st₀ : TRState)
    (c c' : RecvChain) (seed k_own : DY.Bytes),
    TR.G1.RecvHistInvTR interpretation S g r₀ ms₁ →
    TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁) →
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body →
    parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ¬ReselectCollision interpretation r₀ S g ms₁ t₀ →
    st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁) →
    c ∈ st₀.recv →
    gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList →
    c.ratchetKey.AttackerKnows (runTraceMoves r₀ ms₁) →
    consumeMessageKey c msg₀.counter = some (seed, c') →
    k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₀ →
    body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire) →
    ∃ (t₁ : DY.Bytes) (msg₁ : TRSignalMsg),
      t₁ ∈ recvRepresentations interpretation r₀ S g ms₁ body ∧
      parseTrSignalMsg t₁ = some msg₁ ∧ msg₁.version = messageVersion ∧
      msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
      recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms₁) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
      ¬RecvCollision interpretation r₀ S g ms₁ t₁

theorem rcv_byteChainReselectAt_of_c16
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms₁ : List Move) (τ₁ : List MachineEvent) :
    RcvByteChainReselectAt interpretation r₀ S g ms₁ τ₁ := by
  intro body m t₀ msg₀ st₀ c c' seed k_own hHist _hIW htry ht₀ hparse₀ hver₀ hNotCol₀ hNotRS₀
    hst₀ hc_mem hγ_pk hrkK hcons₀ hk_own hMacBytes
  obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, _hct₁, _hpq₁, hseed₁, hk₁, hMac₁, hNC₁⟩ :=
    TR.reselect_of_not_reselectCollision hHist htry ht₀ hparse₀ hver₀ hNotCol₀ hNotRS₀ hst₀ hc_mem
      hγ_pk hrkK hcons₀ hk_own hMacBytes
  exact ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hseed₁, hk₁, hMac₁, hNC₁⟩

/-- Non-junk `SkippedKeyStored` provenance and non-low-order ratchet-key supply. -/
def RcvSkippedNotJunkSeedProvAt
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms₁ : List Move) : Prop :=
  ∀ (p : Participant) (st₀ st_prov : TRState) (m : SignalMessage) (pk seed : DY.Bytes)
    (rIdx srcIdx skIdx : Nat),
    st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) →
    (∀ msg, msg.version = messageVersion → msg.ratchetKey = pk →
      msg.counter = UInt32.ofBitVec m.counter → recvSeed st_prov msg = some seed) →
    (runTraceMoves r₀ ms₁).EventLoggedAt
      (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx →
    gamma interpretation S g pk = m.senderRatchetKey.bytes.toList →
    ¬TR.G1.JunkTR pk →
    TR.RkKnownOrInit (runTraceMoves r₀ ms₁) pk ∧
    (∀ c₀ : RecvChain, recvChainFor st_prov.toDRState pk = some (c₀, true) →
      ∃ (st₁_post : TRState) (c₁ : RecvChain),
        st₁_post ∈ availableStates r₀ (runTraceMoves r₀ ms₁) ∧
        c₁ ∈ st₁_post.recv ∧ c₁.ratchetKey = pk ∧
        DY.X25519.isLowOrderKey ((gamma interpretation S g pk).map BitVec.toNat) = false)

theorem rcv_skippedNotJunkSeedProvAt_of_notLowAll
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms₁ : List Move}
    (hreach : (runTraceMoves r₀ ms₁).Reachable reachability)
    (hlow : TR.RecvRkNotLowAll interpretation S g r₀ ms₁) :
    RcvSkippedNotJunkSeedProvAt interpretation r₀ S g ms₁ := by
  intro p st₀ _st_prov m pk seed rIdx srcIdx skIdx _hst_prov _hseed_m hlog _hγ_pk _hJunk
  obtain ⟨hrkK, ⟨_p₁, st₁_post, _i₁, c₁, hst₁_at, hc₁_mem, hc₁_rk, _, _⟩, _⟩ :=
    provEvTR_reachable hreach (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx skIdx hlog
  have hst₁_avail : st₁_post ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
    TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms₁ hst₁_at
  have hNotLow : DY.X25519.isLowOrderKey ((gamma interpretation S g pk).map BitVec.toNat) = false := by
    rw [← hc₁_rk]
    exact hlow st₁_post hst₁_avail c₁ hc₁_mem
  exact ⟨Or.inl hrkK, fun _c₀ _hrcf => ⟨st₁_post, c₁, hst₁_avail, hc₁_mem, hc₁_rk, hNotLow⟩⟩

/-- Dispatches a verified Whisper message seed into attacker knowledge or `AuthenticDecryptRepB3_g1`. -/
theorem rcv_g1_authentic_or_seed_known
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes) (parsed : SignalMessage)
    (hSkel : TR.G1.HonestSkelUniq interpretation r₀ S g ms)
    (hABS' : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hTryFrom : SignalMessage.tryFrom protoSignalCodec b = .ok parsed)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes) (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : b.drop (b.length - 8) =
      gamma interpretation S g
        (computeMac (trMsgKeys k_own mkSeed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [parsed.ciphertext,
       gamma interpretation S g (trMsgKeys k_own mkSeed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own mkSeed).iv).take 16] = some ptext) :
    mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
    TR.G1.AuthenticDecryptRepB3_g1 interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
  have hIk := TR.G1.Ik.availableIkShapeId_all r₀ ms
  rcases TR.G1.g1a_case_split interpretation r₀ S g ms b t₀ msg₀ hreach ht₀ hparse₀
      hNotCol st₀ hst₀ mkSeed hseed k_own hk_own hMacBytes with
    hSeedKnows | hCaseB | hCaseC
  · exact Or.inl hSeedKnows
  · obtain ⟨salt₁, hsalt₁, hTripleEq, pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s,
      ns_s, pn_s, hmac_eq, htrunc_ak, hsh_inp⟩ := hCaseB
    let wire_s := trHonestWireMsg (DY.DiffieHellman.dhPk a_s) ns_s pn_s
      (DY.SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
    let inp₀ := hmac (trMsgKeys pqSalt_s seed_s).macKey
      (DY.Concat.concat myIk_s (DY.Concat.concat peerIk_s wire_s))
    have hDecOk_salt₁ : interpretation aesCbcDecryptSymbol
        [parsed.ciphertext,
         gamma interpretation S g (trMsgKeys salt₁ mkSeed).cipherKey,
         (gamma interpretation S g (trMsgKeys salt₁ mkSeed).iv).take 16] = some ptext := by
      rw [hTripleEq.1, hTripleEq.2.2]
      exact hDecOk
    rcases TR.G1.g1b_honest_send_branch_strong interpretation hEq r₀ S g ms b ptext parsed
        hSkel hIk hreach hTryFrom t₀ msg₀ ht₀ hparse₀ st₀ hst₀ mkSeed hseed salt₁
        hDecOk_salt₁ salt₁ inp₀ rfl hmac_eq htrunc_ak hsh_inp with
      hinp_ak | hAuth
    · exact TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
        t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own
        ⟨salt₁, inp₀, hsalt₁, hTripleEq, hmac_eq, hinp_ak, hsh_inp⟩
    · exact Or.inr ⟨salt₁, hsalt₁, hTripleEq, hAuth⟩
  · exact TR.G1.g1c_own_key_branch' interpretation r₀ S g ms b ptext hABS' hreach
      t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ mkSeed hseed k_own hCaseC

theorem rcv_skippedVar_of_rk_eq
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (body ptBytes : HwBytes) (m : SignalMessage) (st₀ : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg)
    (hSkel : TR.G1.HonestSkelUniq interpretation r₀ S g ms)
    (hABS' : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hctr₀ : msg₀.counter = UInt32.ofBitVec m.counter)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hrk₀ : msg₀.ratchetKey = pk)
    (hseed : recvSeed st₀ msg₀ = some seed)
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hDecOk : interpretation aesCbcDecryptSymbol
      [m.ciphertext, gamma interpretation S g (trMsgKeys k_own seed).cipherKey,
       (gamma interpretation S g (trMsgKeys k_own seed).iv).take 16] = some ptBytes) :
    SkippedVarConcl interpretation r₀ S g ms body ptBytes m st₀ pk seed k_own :=
  ⟨t₀, msg₀, ht₀, hparse₀, hver₀, hrk₀, hctr₀, hMacBytes,
    rcv_g1_authentic_or_seed_known interpretation hEq r₀ S g ms body ptBytes m hSkel hABS'
      hreach htry t₀ msg₀ ht₀ hparse₀ hNotCol st₀ hst₀ seed hseed k_own hk_own hMacBytes hDecOk⟩

theorem rcv_hPkDNR_of_reselect
    {interpretation : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interpretation)
    {r₀ : ProtocolSetup} (_hwf : ProtocolSetupWF r₀) {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {g' : Ghost} {ms₁ : List Move} {τ₁ : List MachineEvent}
    (_hc : CleanBy interpretation r₀ S who ok g' ms₁ τ₁)
    (hSkel : TR.G1.HonestSkelUniq interpretation r₀ S g' ms₁)
    (hABS' : TR.G1.G1cAttackerBuiltSeedExcl' interpretation r₀ S g' ms₁)
    (hRes : RcvByteChainReselectAt interpretation r₀ S g' ms₁ τ₁) :
    TR.RecvDecStepAt.NoRatchetPkDispatchAtSt interpretation r₀ S g' ms₁ τ₁ := by
  intro p stateIdx₀ body ptBytes m st₀ c c' t₀ seed k_own msg₀
    _hRun hreach htry ht₀ hparse₀ hver₀ hctr₀ hNotCol hNotRS
    hst₀_get hc_mem hcons₀ hseed_c hk_own hHist hIW hrk_oi hγ_pk hMacBytes _hPeerK _hMyK hDecOk
  have hst₀_at : TR.G1.TRStateStoredAt p st₀ stateIdx₀ (runTraceMoves r₀ ms₁) :=
    Symbolic.Swarm.CREF.TR.FreshSigma.at?_eq_some_of_getLocalState_some hst₀_get
  have hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁) :=
    TR.G1.mem_availableStates_of_trStateStoredAt r₀ ms₁ hst₀_at
  have hseed_kdf : ∃ ck, seed = (DY.Libsignal.TripleRatchet.kdfCk ck).2 :=
    exists_kdfCk_of_consumeMessageKey hcons₀
  have hResel : c.ratchetKey.AttackerKnows (runTraceMoves r₀ ms₁) →
      SkippedVarConcl interpretation r₀ S g' ms₁ body ptBytes m st₀ c.ratchetKey seed k_own := by
    intro hrkK
    obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hseed₁, hk_own₁, hMacBytes₁, hNotCol₁⟩ :=
      hRes body m t₀ msg₀ st₀ c c' seed k_own hHist hIW htry ht₀ hparse₀ hver₀ hNotCol
        hNotRS hst₀ hc_mem hγ_pk hrkK hcons₀ hk_own hMacBytes
    exact rcv_skippedVar_of_rk_eq interpretation hEq r₀ S g' ms₁ body ptBytes m st₀
      t₁ c.ratchetKey seed k_own msg₁ hSkel hABS' hreach htry ht₁ hparse₁
      hver₁ (hctr₁.trans hctr₀) hNotCol₁ hst₀ hrk₁ hseed₁ hk_own₁ hMacBytes₁ hDecOk
  have hConcl : SkippedVarConcl interpretation r₀ S g' ms₁ body ptBytes m st₀ c.ratchetKey seed k_own := by
    by_cases hrk₀ : msg₀.ratchetKey = c.ratchetKey
    · exact rcv_skippedVar_of_rk_eq interpretation hEq r₀ S g' ms₁ body ptBytes m st₀
        t₀ c.ratchetKey seed k_own msg₀ hSkel hABS' hreach htry ht₀ hparse₀ hver₀ hctr₀ hNotCol
        hst₀ hrk₀ (hseed_c hrk₀) hk_own hMacBytes hDecOk
    · have hγ_msg₀ : gamma interpretation S g' msg₀.ratchetKey = gamma interpretation S g' c.ratchetKey :=
        (((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1).trans hγ_pk.symm
      by_cases hCaseA' : TR.G1.CaseA' c.ratchetKey
      · rcases hVar : c.ratchetKey.view? DY.X25519.Variant.SubF with _ | _
        · exact absurd (TR.G1.rk_eq_of_noncolliding_caseA' interpretation hEq r₀ S g' ms₁ hHist hIW
            hst₀ hc_mem hCaseA' hVar hparse₀ hver₀ hγ_msg₀ hNotCol) hrk₀
        · exact hResel (rk_attackerKnows_of_rkKnownOrInit_variant hrk_oi hVar)
      · exact hResel (rk_attackerKnows_of_rkKnownOrInit_litJunk hrk_oi (TR.G1.junkTR_of_caseB' hCaseA'))
  obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hMacBytes₁, hDisj⟩ := hConcl
  obtain ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂, hMacBytes₂, hOut⟩ :=
    g1_disj_to_salt_form_at interpretation r₀ S g' ms₁ body ptBytes m
      st₀ t₁ c.ratchetKey seed k_own msg₁ hreach hseed_kdf ht₁ hparse₁ hver₁ hrk₁ hMacBytes₁ hDecOk hDisj
  exact ⟨t₂, msg₂, ht₂, hparse₂, hver₂, hrk₂, hctr₂.trans (hctr₁.trans hctr₀.symm), hMacBytes₂, hOut⟩

open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)
open DY.Libsignal.HwEvents (MachineEvent)
open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.Symbolic.Swarm.CREF.TR _root_.Symbolic.Swarm.CREF.CliPure.TR

theorem rcv_hfresh_of_cleanBy (interpretation : ExternInterpretation)
    {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ms : List Move} {acc : List MachineEvent}
    (hc : CleanBy interpretation r₀ S who ok g ms acc) : TRRecvFreshAll r₀ ms :=
  trRecvFreshAll_of_matchedPrefix interpretation hc.matched

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
