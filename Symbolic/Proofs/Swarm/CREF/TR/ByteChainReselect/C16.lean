/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
public import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.ByteChainReselect.WireRebuild

/-!
# Byte-Chain Reselection Without Collision

Proves `reselect_of_not_reselectCollision`: when a stored receive chain `c` of an available
state matches the received message's ratchet key in bytes and neither `RecvCollision` nor
`ReselectCollision` holds on `t₀`, there exists a non-colliding representation `t₁` naming
`c.ratchetKey` with identical wire and MAC bytes, `recvSeed`, and `ownKeys`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey computeMac messageVersion)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

/-- If `rk ∈ storedRatchetKeys` matches `msg₀.ratchetKey` in bytes with `rk ≠ msg₀.ratchetKey` and
`¬ ReselectCollision` holds on `t₀`, then any `rk`-reselected representation yields a non-colliding
`rk`-reselected representation. -/
theorem reselectCollision_transfer
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {body : HwBytes} {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotRS₀ : ¬ ReselectCollision interpretation r₀ S g ms t₀)
    {rk : DY.Bytes} (hrk_mem : rk ∈ storedRatchetKeys r₀ (runTraceMoves r₀ ms) msg₀)
    (hγrk : gamma interpretation S g rk = gamma interpretation S g msg₀.ratchetKey)
    (hne : rk ≠ msg₀.ratchetKey)
    (hEx : ∃ t' ∈ recvRepresentations interpretation r₀ S g ms body,
      ∃ msg', parseTrSignalMsg t' = some msg' ∧ ReselectsTo msg₀ msg' rk) :
    ∃ t₁ ∈ recvRepresentations interpretation r₀ S g ms body,
      ∃ msg₁, parseTrSignalMsg t₁ = some msg₁ ∧ ReselectsTo msg₀ msg₁ rk ∧
        ¬RecvCollision interpretation r₀ S g ms t₁ := by
  have hbody : gamma interpretation S g t₀ = body := ht₀.2.1
  by_contra hall
  apply hNotRS₀
  refine ⟨msg₀, hparse₀, rk, hrk_mem, hγrk, hne, ?_, ?_⟩
  · rw [hbody]; exact hEx
  · rw [hbody]
    intro t' ht' msg' hp' hR'
    by_contra hnc
    exact hall ⟨t', ht', msg', hp', hR', hnc⟩

theorem chain_rk_mem_storedRatchetKeys {r₀ : ProtocolSetup} {tr : ExecTrace} {msg : TRSignalMsg}
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ tr) {c : RecvChain} (hc : c ∈ st₀.recv) :
    c.ratchetKey ∈ storedRatchetKeys r₀ tr msg := by
  unfold storedRatchetKeys
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨st₀, hst₀, List.mem_map.mpr ⟨c, hc, rfl⟩⟩)

theorem bcrC16_consumer_facts
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {body : HwBytes} {msg₀ msg₁ : TRSignalMsg} {t₁ : DY.Bytes}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    (ht₀w : gamma interpretation S g msg₀.wire = body.take (body.length - 8))
    (ht₁ : t₁ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₁ : parseTrSignalMsg t₁ = some msg₁)
    (hver₀ : msg₀.version = messageVersion)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv) {seed k_own : DY.Bytes}
    (hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hR : ReselectsTo msg₀ msg₁ c.ratchetKey) :
    msg₁.version = messageVersion ∧ recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g
          (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) := by
  obtain ⟨hrk₁, hver₁, hctr₁, _, hpq₁⟩ := hR
  have hver₁' : msg₁.version = messageVersion := hver₁.trans hver₀
  have hγw : gamma interpretation S g msg₁.wire = gamma interpretation S g msg₀.wire :=
    (ht₁.2.2.2 msg₁ hparse₁).1.trans ht₀w.symm
  refine ⟨hver₁', ?_, ?_, ?_⟩
  · exact bcrWireRebuild_recvSeed_eq_some_of_mem_hist hHist hst₀ hc_mem hver₁' hrk₁
      (hctr₁.symm ▸ hcons₀)
  · unfold ownKeys at hk_own ⊢; rw [hpq₁]; exact hk_own
  · rw [bcrWireRebuild_gamma_computeMac_congr_wire interpretation S g _ _ _ msg₁.wire msg₀.wire hγw]
    exact hMacBytes

theorem bcrC16_reselect_core
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {body : HwBytes} {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hNotCol₀ : ¬RecvCollision interpretation r₀ S g ms t₀)
    (hNotRS₀ : ¬ ReselectCollision interpretation r₀ S g ms t₀)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv)
    (hγrk : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg₀.ratchetKey)
    {seed k_own : DY.Bytes}
    (hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire))
    (hEx : c.ratchetKey ≠ msg₀.ratchetKey →
      ∃ t' ∈ recvRepresentations interpretation r₀ S g ms body,
        ∃ msg', parseTrSignalMsg t' = some msg' ∧ ReselectsTo msg₀ msg' c.ratchetKey) :
    ∃ t₁ msg₁, t₁ ∈ recvRepresentations interpretation r₀ S g ms body ∧
      parseTrSignalMsg t₁ = some msg₁ ∧ msg₁.version = messageVersion ∧
      msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
      msg₁.ciphertext = msg₀.ciphertext ∧ msg₁.pqRatchet = msg₀.pqRatchet ∧
      recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
      ¬RecvCollision interpretation r₀ S g ms t₁ := by
  have ht₀w := (ht₀.2.2.2 msg₀ hparse₀).1
  have key : ∃ t₁ ∈ recvRepresentations interpretation r₀ S g ms body,
      ∃ msg₁, parseTrSignalMsg t₁ = some msg₁ ∧ ReselectsTo msg₀ msg₁ c.ratchetKey ∧
        ¬RecvCollision interpretation r₀ S g ms t₁ := by
    by_cases heq : c.ratchetKey = msg₀.ratchetKey
    · exact ⟨t₀, ht₀, msg₀, hparse₀, ⟨heq.symm, rfl, rfl, rfl, rfl⟩, hNotCol₀⟩
    · exact reselectCollision_transfer ht₀ hparse₀ hNotRS₀ (chain_rk_mem_storedRatchetKeys hst₀ hc_mem) hγrk heq
        (hEx heq)
  obtain ⟨t₁, ht₁, msg₁, hparse₁, hR, hnc⟩ := key
  obtain ⟨hver₁, hseed₁, hk₁, hMac₁⟩ :=
    bcrC16_consumer_facts hHist ht₀w ht₁ hparse₁ hver₀ hst₀ hc_mem hcons₀ hk_own hMacBytes hR
  obtain ⟨hrk₁, _, hctr₁, hct₁, hpq₁⟩ := hR
  exact ⟨t₁, msg₁, ht₁, hparse₁, hver₁, hrk₁, hctr₁, hct₁, hpq₁, hseed₁, hk₁, hMac₁, hnc⟩

/-- Under `¬ RecvCollision` and `¬ ReselectCollision` on `t₀`, any stored receive chain `c` matching
the sender ratchet key in bytes yields a non-colliding representation naming `c.ratchetKey` that
preserves the message fields, `recvSeed`, `ownKeys`, and MAC bytes. -/
theorem reselect_of_not_reselectCollision
    {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move}
    {body : HwBytes} {m : SignalMessage}
    (hHist : G1.RecvHistInvTR interpretation S g r₀ ms)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    {t₀ : DY.Bytes} {msg₀ : TRSignalMsg}
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (hNotCol₀ : ¬RecvCollision interpretation r₀ S g ms t₀)
    (hNotRS₀ : ¬ReselectCollision interpretation r₀ S g ms t₀)
    {st₀ : TRState} (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    {c c' : RecvChain} (hc_mem : c ∈ st₀.recv)
    (hγ_pk : gamma interpretation S g c.ratchetKey = m.senderRatchetKey.bytes.toList)
    (hrkK : c.ratchetKey.AttackerKnows (runTraceMoves r₀ ms))
    {seed k_own : DY.Bytes}
    (hcons₀ : consumeMessageKey c msg₀.counter = some (seed, c'))
    (hk_own : k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₀)
    (hMacBytes : body.drop (body.length - 8) =
      gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₀.wire)) :
    ∃ t₁ msg₁, t₁ ∈ recvRepresentations interpretation r₀ S g ms body ∧
      parseTrSignalMsg t₁ = some msg₁ ∧ msg₁.version = messageVersion ∧
      msg₁.ratchetKey = c.ratchetKey ∧ msg₁.counter = msg₀.counter ∧
      msg₁.ciphertext = msg₀.ciphertext ∧ msg₁.pqRatchet = msg₀.pqRatchet ∧
      recvSeed st₀ msg₁ = some seed ∧
      k_own ∈ ownKeys r₀ (runTraceMoves r₀ ms) st₀ msg₁ ∧
      body.drop (body.length - 8) =
        gamma interpretation S g (computeMac (trMsgKeys k_own seed).macKey st₀.peerIk st₀.myIk msg₁.wire) ∧
      ¬RecvCollision interpretation r₀ S g ms t₁ := by
  have hrk₀ : gamma interpretation S g msg₀.ratchetKey = m.senderRatchetKey.bytes.toList :=
    ((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1
  refine bcrC16_reselect_core hHist ht₀ hparse₀ hver₀ hNotCol₀ hNotRS₀ hst₀ hc_mem
    (hγ_pk.trans hrk₀.symm) hcons₀ hk_own hMacBytes ?_
  intro _
  obtain ⟨t₁, msg₁, -, hR, -, -, -⟩ :=
    reselect_exists_mac_eq_unbundled hHist htry ht₀ hparse₀ hver₀ hst₀ (c' := c') hc_mem hγ_pk hrkK
      hcons₀ hk_own hMacBytes
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hver₁, hrk₁, hctr₁, hct₁, hpq₁, _, ht₁, hparse₁⟩ := hR
  exact ⟨t₁, ht₁, msg₁, hparse₁, hrk₁, hver₁, hctr₁, hct₁, hpq₁⟩

end Symbolic.Swarm.CREF.TR
