/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTRStrong
public import Symbolic.Proofs.Swarm.CREF.TR.SkippedVarFresh
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Fresh-Alias Exclusion Predicate for Skipped Keys

Defines `SkippedFreshAliasExclB` and auxiliary congruence/inversion lemmas for `recvSeed` and
`SkippedVarConcl`.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain recvChainFor findRecvChain consumeMessageKey computeMac
  messageVersion)
open DY.Libsignal.TripleRatchet
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR.RecvDecStep.SkippedVarKnownCk (SkippedVarConcl)

theorem snjf_recvChainFor_of_recvSeed {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (h : recvSeed st msg = some seed) :
    ∃ (c₀ : RecvChain) (b : Bool) (c₀' : RecvChain),
      recvChainFor st.toDRState msg.ratchetKey = some (c₀, b) ∧
      consumeMessageKey c₀ msg.counter = some (seed, c₀') := by
  unfold recvSeed at h
  split at h
  · split at h
    · cases h
    · next c₀ b hrcf =>
      rcases hcons : consumeMessageKey c₀ msg.counter with _ | ⟨s, c₀'⟩
      · rw [hcons] at h; cases h
      · rw [hcons] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨c₀, b, c₀', hrcf, h ▸ hcons⟩
  · cases h

theorem snjf_skippedVarConcl_congr_ik
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {body ptBytes : HwBytes} {m : SignalMessage} {st st' : TRState} {pk seed k_own : DY.Bytes}
    (hpeer : st.peerIk = st'.peerIk) (hmy : st.myIk = st'.myIk)
    (h : SkippedVarConcl interpretation r S g ms body ptBytes m st pk seed k_own) :
    SkippedVarConcl interpretation r S g ms body ptBytes m st' pk seed k_own := by
  obtain ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hMac₁, hDisj⟩ := h
  refine ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hpeer ▸ hmy ▸ hMac₁, ?_⟩
  rcases hDisj with hK | ⟨salt₁, hsalt, hkeys, t', msg', ptTerm, pqSalt, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩
  · exact Or.inl hK
  · exact Or.inr ⟨salt₁, hsalt, hkeys, t', msg', ptTerm, pqSalt, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
      h₈, h₉, h₁₀, hpeer ▸ hmy ▸ h₁₁, h₁₂, h₁₃⟩

/-- Excludes a fresh DH-ratchet alias `pk` whose skipped message key comes from a responder's
initial receive chain with `msg₀.counter < c_src.index`. -/
def SkippedFreshAliasExclB
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms₁ : List Move) (_τ₁ : List MachineEvent) : Prop :=
  ∀ (p : Participant) (stateIdx₀ : Nat) (body : HwBytes) (m : SignalMessage) (st₀ st_prov : TRState)
    (t₀ pk seed k_own : DY.Bytes) (msg₀ : TRSignalMsg) (rIdx srcIdx skIdx : Nat) (c₀ c_ex : RecvChain),
    SignalMessage.tryFrom protoSignalCodec body = .ok m →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms₁ body →
    parseTrSignalMsg t₀ = some msg₀ →
    msg₀.version = messageVersion →
    msg₀.counter = UInt32.ofBitVec m.counter →
    ¬RecvCollision interpretation r₀ S g ms₁ t₀ →
    ((PersistentLocalState.getLocalState p stateIdx₀ : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st₀ →
    st_prov ∈ availableStates r₀ (runTraceMoves r₀ ms₁) →
    (st_prov.peerIk = st₀.peerIk ∧ st_prov.myIk = st₀.myIk) →
    (∀ msg, msg.version = messageVersion → msg.ratchetKey = pk → msg.counter = msg₀.counter → recvSeed st_prov msg = some seed) →
    k_own = ({ st := st₀.spqr, msg := msg₀.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack →
    (runTraceMoves r₀ ms₁).EventLoggedAt (TREvent.SkippedKeyStored (st₀.sessionInfo p) pk (UInt32.ofBitVec m.counter) seed rIdx srcIdx) skIdx →
    gamma interpretation S g pk = m.senderRatchetKey.bytes.toList →
    body.drop (body.length - 8) = gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st_prov.peerIk st_prov.myIk msg₀.wire) →
    recvChainFor st_prov.toDRState pk = some (c₀, true) →
    findRecvChain st_prov.recv msg₀.ratchetKey = some c_ex →
    msg₀.ratchetKey ≠ pk →
    ¬TR.G1.JunkTR pk →
    (∃ x, pk.view? DY.X25519.Variant.SubF = some x) →
    pk.AttackerKnows (runTraceMoves r₀ ms₁) →
    ¬seed.AttackerKnows (runTraceMoves r₀ ms₁) →
    (∃ (p₀ : Participant) (st₀_src : TRState) (c_src : RecvChain),
      TR.G1.TRStateStoredAt p₀ st₀_src srcIdx (runTraceMoves r₀ ms₁) ∧ st₀_src.sessionInfo p₀ = st₀.sessionInfo p ∧
      st₀_src.initiator = false ∧ c_src ∈ st₀_src.recv ∧ c_src.ratchetKey = pk ∧ c_src.rIdx = rIdx ∧
      UInt32.ofBitVec m.counter < c_src.index) →
    False

end Symbolic.Swarm.CREF.CliPure
