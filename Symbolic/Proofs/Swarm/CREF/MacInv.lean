/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.KdfExtract
import Symbolic.Specifications.Model.EquationalTheory.Trunc
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRkCore
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.CREF.ModelMono
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HmacWireMemo
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSendBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.NotOpaqueMac
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.RkSpine -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpineRkK -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Whisper and Pre-Key MAC Inversion and Spine Lemmas

Proves 3-stage KDF attacker-knowledge inversion (`hmac_wire_attackerKnows_inv_memo_of_kdf`),
pre-key MAC case splitting under `bobTrials` (`bs_g1a_case_split`), and opposite-parity spine
equality on `LoggedOrBobIkmRk` (`oppParity_of_spineRk_bob`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

/-- Bob's initial pre-key receive chain (`Stage1Trials.bobInitChain`). -/
abbrev bobChain := Stage1Trials.bobInitChain

end Symbolic.Swarm.CREF

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (computeMac trMsgKeys)
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR.G1.Spine (memo_mem_of_kdfExtract_left memo_mem_of_kdfExtract_right)

end Symbolic.Swarm.CREF.TR.G1

namespace Symbolic.Swarm.CREF.MacInv

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys trHonestWireMsg)
open DY.Libsignal.TripleRatchet (RecvChain createChain consumeMessageKey skippedSeeds computeMac
  hmac kdfCk kdfRk lit litByte)
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhIkm agree errToOption serializedIk)
open Symbolic.Swarm.CREF.TR.G1
open Symbolic.Swarm.CREF.TR.G1.Spine
open Symbolic.Swarm.CREF.TR.RecvDecStep

attribute [local instance 2000]
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecTrace

/-! ## Re-exports from `TR.G1` and `TR.G1.Spine` -/

export Symbolic.Swarm.CREF.TR.G1 (
  macKdfSafe_c_trunc8_inv
  macKdfSafe_c_trunc8_inv_strong
  hmac_wire_attackerKnows_inv_memo
  memo_mem_of_trunc8
  memo_mem_of_parse_mac
  g1a_case_split
  g1b_honest_send_branch_strong
  g1c_own_key_branch'
  notSpqrHeaded
  notOpaqueHeaded
  notOpaqueHeaded_mac_of_parseTrSignalMsg
  attackerKnows_mac_of_parseTrSignalMsg
  gamma_computeMac_congr_macKey
  stRkSpine_of_stored
)

export Symbolic.Swarm.CREF.TR.G1.Spine (
  SpineRk
  SpineRkK
  LoggedIkmRk
  eq_of_shape_eq_of_spineRk
  spStateRk_runTrace
  spineRk_send_runTrace
  spineRk_recvSeed_runTrace
  spStateRkK_runTrace
  spineRkK_recvSeed_runTrace
)

/-! ## General 3-stage KDF inversion -/

theorem consumeMessageKey_eq_some_kdfExtract :
    ∀ (c : RecvChain) (ctr : UInt32) (seed : DY.Bytes) (c' : RecvChain),
      consumeMessageKey c ctr = some (seed, c') →
      ∃ ck : DY.Bytes, seed = KdfExtract.kdfExtract ck (litByte 0x01) ∧
        c'.chainKey = KdfExtract.kdfExtract ck (litByte 0x02) := by
  intro c ctr seed c' hcmk
  unfold consumeMessageKey at hcmk
  split at hcmk
  · cases hcmk
  · split at hcmk
    · cases hcmk
    · split at hcmk
      · cases hcmk
      · injection hcmk with hcmk
        injection hcmk with h1 h2
        exact ⟨_, h1.symm, by rw [← h2]; rfl⟩

/-- Three-stage KDF attacker-knowledge inversion: if `msg₀.mac = Trunc.trunc8 inp₀` is
attacker-known with `(gamma' inp₀).shape` matching `hmac (trMsgKeys salt₁ seed₁).macKey ...` for
`seed₁ = KdfExtract.kdfExtract ck₁ (litByte 0x01)`, then there exist attacker-known `salt₀, seed₀`
matching the shapes of `salt₁, seed₁` whose memos lie in the memo of `t₀`. -/
theorem hmac_wire_attackerKnows_inv_memo_of_kdf
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (ck₁ salt₁ seed₁ peerIk myIk inp₀ : DY.Bytes)
    (hseed₁ : seed₁ = KdfExtract.kdfExtract ck₁ (litByte 0x01))
    (hmac₀ : msg₀.mac = Trunc.trunc8 inp₀)
    (hinp_ak : inp₀.AttackerKnows (runTraceMoves r₀ ms))
    (hsh : (gamma' interpretation S g inp₀).shape =
      (gamma' interpretation S g (hmac (trMsgKeys salt₁ seed₁).macKey
        (Concat.concat peerIk (Concat.concat myIk msg₀.wire)))).shape) :
    ∃ salt₀ seed₀ : DY.Bytes,
      salt₀.AttackerKnows (runTraceMoves r₀ ms) ∧ seed₀.AttackerKnows (runTraceMoves r₀ ms) ∧
      (gamma' interpretation S g salt₀).shape = (gamma' interpretation S g salt₁).shape ∧
      (gamma' interpretation S g seed₀).shape = (gamma' interpretation S g seed₁).shape ∧
      (∀ e ∈ (gamma' interpretation S g (KdfExtract.kdfExtract salt₀ seed₀)).memo,
        e ∈ (gamma' interpretation S g t₀).memo) ∧
      (∀ e ∈ (gamma' interpretation S g seed₀).memo, e ∈ (gamma' interpretation S g t₀).memo) := by
  let T := runTraceMoves r₀ ms
  have hmemo_inp : ∀ e ∈ (gamma' interpretation S g inp₀).memo,
      e ∈ (gamma' interpretation S g t₀).memo :=
    fun _ he => memo_mem_of_parse_mac interpretation S g hparse₀ hmac₀ he
  obtain ⟨x₀, _hsplit, _hx₀, hpack, _hrk_eq, _hct_eq, _hpq_eq⟩ := parseTrSignalMsg_unpack_c hparse₀
  have hpack_wire : msg₀.wire = DY.TrWire.trWireMsg x₀.version x₀.senderRatchetKey
      x₀.counter x₀.previousCounter x₀.ciphertext x₀.pqRatchet x₀.encodingVariation := hpack
  obtain ⟨s₀, i₀, hs₀_sh, hi₀_sh, hinp_eq⟩ := kdfExtract_shape_eq_inv_c interpretation S g hsh
  have hinp_kdf_ak : (KdfExtract.kdfExtract s₀ i₀).AttackerKnows T := hinp_eq ▸ hinp_ak
  rw [shape_concat_tr, shape_concat_tr] at hi₀_sh
  have hs₀_ak : s₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms s₀ i₀ hreach hinp_kdf_ak with
      ⟨hs₀_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hs₀_ak
    · rw [h01] at hi₀_sh; unfold litByte at hi₀_sh; rw [shape_literalToBytes] at hi₀_sh
      exact False.elim (literal_ne_concat _ _ _ hi₀_sh)
    · rw [h02] at hi₀_sh; unfold litByte at hi₀_sh; rw [shape_literalToBytes] at hi₀_sh
      exact False.elim (literal_ne_concat _ _ _ hi₀_sh)
    · rw [hwr1, shape_concat_tr] at hi₀_sh
      have h2 := (concat_injective hi₀_sh).2
      unfold litByte at h2; rw [shape_literalToBytes] at h2
      exact False.elim (literal_ne_concat _ _ _ h2)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> {
        rw [hwr2, shape_concat_tr, shape_concat_tr] at hi₀_sh
        have h3 := (concat_injective (concat_injective hi₀_sh).2).2
        unfold litByte at h3; rw [shape_literalToBytes, hpack_wire, shape_trWireMsg_tr] at h3
        exact False.elim (literal_ne_trWireMsg _ _ _ _ _ _ _ _ h3)
      }
  have hmemo_s₀ : ∀ e ∈ (gamma' interpretation S g s₀).memo,
      e ∈ (gamma' interpretation S g t₀).memo :=
    fun _ he => hmemo_inp _ (hinp_eq ▸ memo_mem_of_kdfExtract_left interpretation S g _ _ he)
  obtain ⟨prk₀, info₂₀, hprk₀_sh, hinfo₂₀_sh, hs₀_eq⟩ :=
    kdfExtract_shape_eq_inv_c interpretation S g hs₀_sh
  have hs₀_kdf_ak : (KdfExtract.kdfExtract prk₀ info₂₀).AttackerKnows T := hs₀_eq ▸ hs₀_ak
  rw [shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
  have hprk₀_ak : prk₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms prk₀ info₂₀ hreach hs₀_kdf_ak with
      ⟨hprk₀_ak, _⟩ | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hprk₀_ak
    · rw [h01] at hinfo₂₀_sh; unfold litByte at hinfo₂₀_sh; rw [shape_literalToBytes] at hinfo₂₀_sh
      exact False.elim (literal_ne_concat _ _ _ hinfo₂₀_sh)
    · rw [h02] at hinfo₂₀_sh; unfold litByte at hinfo₂₀_sh; rw [shape_literalToBytes] at hinfo₂₀_sh
      exact False.elim (literal_ne_concat _ _ _ hinfo₂₀_sh)
    · rw [hwr1, shape_concat_tr] at hinfo₂₀_sh
      have h2 := (concat_injective hinfo₂₀_sh).2
      unfold litByte at h2; rw [shape_literalToBytes] at h2
      exact False.elim (literal_ne_concat _ _ _ h2)
    · have hwmk_sh : (gamma' interpretation S g (lit "WhisperMessageKeys")).shape =
          lit "WhisperMessageKeys" :=
        shape_literalToBytes interpretation S g _
      have hpq_sh : (gamma' interpretation S g DY.Libsignal.PQXDH.pqxdhLabel).shape =
          DY.Libsignal.PQXDH.pqxdhLabel :=
        shape_literalToBytes interpretation S g _
      rcases hwr2 with hwr2 | hwr2 | hwr2
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        have hwr_sh : (gamma' interpretation S g (lit "WhisperRatchet")).shape =
            lit "WhisperRatchet" :=
          shape_literalToBytes interpretation S g _
        rw [hwr_sh, hwmk_sh] at h2
        exact False.elim (lit_whisperRatchet_ne_whisperMessageKeys h2)
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        rw [hpq_sh, hwmk_sh] at h2
        exact False.elim (pqxdhLabel_ne_whisperMessageKeys h2)
      · rw [hwr2, shape_concat_tr, shape_concat_tr] at hinfo₂₀_sh
        have h2 := (concat_injective (concat_injective hinfo₂₀_sh).2).1
        rw [hpq_sh, hwmk_sh] at h2
        exact False.elim (pqxdhLabel_ne_whisperMessageKeys h2)
  have hmemo_prk₀ : ∀ e ∈ (gamma' interpretation S g prk₀).memo,
      e ∈ (gamma' interpretation S g t₀).memo :=
    fun _ he => hmemo_s₀ _ (hs₀_eq ▸ memo_mem_of_kdfExtract_left interpretation S g _ _ he)
  obtain ⟨salt₀, seed₀, hsalt₀_sh, hseed₀_sh, hprk₀_eq⟩ :=
    kdfExtract_shape_eq_inv_c interpretation S g hprk₀_sh
  have hprk₀_kdf_ak : (KdfExtract.kdfExtract salt₀ seed₀).AttackerKnows T := hprk₀_eq ▸ hprk₀_ak
  have hseed₁_sh : (gamma' interpretation S g seed₁).shape =
      KdfExtract.kdfExtract (gamma' interpretation S g ck₁).shape
        (gamma' interpretation S g (litByte 0x01)).shape := by
    rw [hseed₁, shape_kdfExtract_tr]
  have h0_ak : salt₀.AttackerKnows T ∧ seed₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms salt₀ seed₀ hreach hprk₀_kdf_ak with
      hboth | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hboth
    · rw [h01, hseed₁_sh] at hseed₀_sh; unfold litByte at hseed₀_sh
      rw [shape_literalToBytes] at hseed₀_sh
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh)
    · rw [h02, hseed₁_sh] at hseed₀_sh; unfold litByte at hseed₀_sh
      rw [shape_literalToBytes] at hseed₀_sh
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh)
    · rw [hwr1, hseed₁_sh, shape_concat_tr] at hseed₀_sh
      exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> {
        rw [hwr2, hseed₁_sh, shape_concat_tr] at hseed₀_sh
        exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh)
      }
  refine ⟨salt₀, seed₀, h0_ak.1, h0_ak.2, hsalt₀_sh, hseed₀_sh,
    fun _ he => hmemo_prk₀ _ (hprk₀_eq ▸ he),
    fun _ he => hmemo_prk₀ _
      (hprk₀_eq ▸ memo_mem_of_kdfExtract_right interpretation S g _ _ he)⟩

/-! ## Pre-key MAC inversion via `bobTrials` -/

theorem bobOpk?_of_bobKeys {r : ProtocolSetup} {p : PreKeyFields} {x : PreKeyRep}
    {keys : HandshakeKeys} (hbk : bobKeys r p x = some keys) :
    ∃ opk, Stage1Trials.bobOpk? r p = some opk ∧ keys = Stage1Trials.bobHandshakeKeys r opk x := by
  unfold bobKeys at hbk
  rcases hopk : Stage1Trials.bobOpk? r p with _ | opk
  · rw [hopk] at hbk; cases hbk
  · rw [hopk] at hbk
    simp only [Option.map_some, Option.some.injEq] at hbk
    exact ⟨opk, rfl, hbk.symm⟩

/-- Pre-MAC handshake guard Boolean for `(r, tr, p, x, msg)` when `bobOpk? r p` is defined. -/
def BobTrialGuard (r : ProtocolSetup) (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep)
    (msg : TRSignalMsg) : Bool :=
  (Stage1Trials.bobOpk? r p).any (Stage1Trials.bobTrialGuard r tr p x msg)

/-- Flattened trial terms `(bobTrials r tr p x msg).flatMap (trialTerms salts msg)` for Bob's pre-key receive. -/
abbrev bobTrialTerms (r : ProtocolSetup) (tr : ExecTrace) (salts : List DY.Bytes) (p : PreKeyFields)
    (x : PreKeyRep) (msg : TRSignalMsg) : List DY.Bytes :=
  (bobTrials r tr p x msg).flatMap (trialTerms salts msg)

theorem computeMac_mem_bobTrialTerms
    (r : ProtocolSetup) (tr : ExecTrace) (salts : List DY.Bytes) (p : PreKeyFields) (x : PreKeyRep)
    (keys : HandshakeKeys) (msg : TRSignalMsg) (seed : DY.Bytes) (c' : RecvChain)
    (salt : DY.Bytes)
    (hbk : bobKeys r p x = some keys)
    (hguard : BobTrialGuard r tr p x msg = true)
    (hcmk : consumeMessageKey (bobChain r keys msg) msg.counter = some (seed, c'))
    (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey
      (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2)) msg.wire ∈
      bobTrialTerms r tr salts p x msg := by
  obtain ⟨opk, hopk, hkeys_eq⟩ := bobOpk?_of_bobKeys hbk
  have hg : Stage1Trials.bobTrialGuard r tr p x msg opk = true := by
    unfold BobTrialGuard at hguard; rwa [hopk, Option.any_some] at hguard
  have hcmk' : consumeMessageKey
      (Stage1Trials.bobInitChain r (Stage1Trials.bobHandshakeKeys r opk x) msg) msg.counter =
      some (seed, c') := hkeys_eq ▸ hcmk
  exact Stage1Trials.computeMac_mem_bobTrialTerms (x := x) (msg := msg) hopk hg hcmk' hsalt

theorem bobTrials_of_bobKeys {r : ProtocolSetup} {tr : ExecTrace} {p : PreKeyFields} {x : PreKeyRep}
    {keys : HandshakeKeys} {msg : TRSignalMsg} {seed : DY.Bytes} {c' : RecvChain}
    (hbk : bobKeys r p x = some keys)
    (hguard : BobTrialGuard r tr p x msg = true)
    (hcmk : consumeMessageKey (bobChain r keys msg) msg.counter = some (seed, c')) :
    bobTrials r tr p x msg =
      [{ peerIk := serializedIk (setupPublic r 0)
         myIk := serializedIk (setupPublic r 2)
         extra := [keys.rk, keys.ck, keys.pqr, (bobChain r keys msg).chainKey, c'.chainKey] ++
           skippedSeeds (bobChain r keys msg) msg.counter
         ownSalts := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
           msg.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
         seed? := some seed }] := by
  obtain ⟨opk, hopk, rfl⟩ := bobOpk?_of_bobKeys hbk
  have hg : Stage1Trials.bobTrialGuard r tr p x msg opk = true := by
    unfold BobTrialGuard at hguard; rwa [hopk, Option.any_some] at hguard
  exact @Stage1Trials.bobTrials_some_some r tr p x msg opk seed c' hopk hg hcmk

theorem exists_honestSalt_of_not_bobOwnSaltMacCollision
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {p : PreKeyFields} {x : PreKeyRep}
    {keys : HandshakeKeys} {msg : TRSignalMsg}
    {seed : DY.Bytes} {c' : RecvChain} {own st' : DY.Bytes}
    (hbk : bobKeys r p x = some keys)
    (hguard : BobTrialGuard r (runTraceMoves r ms) p x msg = true)
    (hcmk : consumeMessageKey (bobChain r keys msg) msg.counter = some (seed, c'))
    (hnot_ak : ¬ seed.AttackerKnows (runTraceMoves r ms))
    (hspqr : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
      msg.pqRatchet (preKeySpqrIndex p) = some (st', own))
    (hmac_gamma : gamma interpretation S g
        (computeMac (trMsgKeys own seed).macKey
          (serializedIk (setupPublic r 0))
          (serializedIk (setupPublic r 2)) msg.wire) =
      gamma interpretation S g msg.mac)
    (hnog : ¬ MacTagForgeryOrCollision interpretation S g
      (fun u => u.AttackerKnows (runTraceMoves r ms)) (honestSalts r ms) msg
      (bobTrials r (runTraceMoves r ms) p x msg)) :
    ∃ salt₁ ∈ honestSalts r ms,
      gamma interpretation S g (trMsgKeys salt₁ seed).cipherKey =
        gamma interpretation S g (trMsgKeys own seed).cipherKey ∧
      gamma interpretation S g (trMsgKeys salt₁ seed).macKey =
        gamma interpretation S g (trMsgKeys own seed).macKey ∧
      gamma interpretation S g (trMsgKeys salt₁ seed).iv =
        gamma interpretation S g (trMsgKeys own seed).iv := by
  have hbt := bobTrials_of_bobKeys hbk hguard hcmk
  have hmem_ctx :
      ({ peerIk := serializedIk (setupPublic r 0)
         myIk := serializedIk (setupPublic r 2)
         extra := [keys.rk, keys.ck, keys.pqr, (bobChain r keys msg).chainKey, c'.chainKey] ++
           skippedSeeds (bobChain r keys msg) msg.counter
         ownSalts := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
           msg.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
         seed? := some seed } : TrialCtx) ∈ bobTrials r (runTraceMoves r ms) p x msg := by
    rw [hbt]; exact List.mem_singleton.mpr rfl
  have hown_mem : own ∈
      ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
        msg.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList := by
    rw [hspqr]; exact List.mem_singleton.mpr rfl
  exact @Stage1Trials.exists_honestSalt_of_not_ownSaltMacCollision
    interpretation S g (fun u => u.AttackerKnows (runTraceMoves r ms)) (honestSalts r ms)
    msg (bobTrials r (runTraceMoves r ms) p x msg) _ seed own hmem_ctx rfl hown_mem hnot_ak hmac_gamma hnog

theorem not_memoCollision_of_noBobStartCollision
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {p : PreKeyFields} {x : PreKeyRep} {msg₀ : TRSignalMsg}
    (hparse : parseTrSignalMsg x.msg = some msg₀)
    (hnc : ¬ BobSessionStartCollidesOrImplicitRejects i r S g ms p x) :
    ¬ MemoCollisionOn i r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
      (runTraceMoves r ms) (runVis r ms)
      ([x.ek, x.ct, x.msg] ++ bobTrialTerms r (runTraceMoves r ms) (honestSalts r ms) p x msg₀) [] := by
  intro hm
  apply hnc
  unfold BobSessionStartCollidesOrImplicitRejects
  rw [hparse]
  exact .inl hm

theorem not_ownSaltMacCollision_of_noBobStartCollision
    {i : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {p : PreKeyFields} {x : PreKeyRep} {msg₀ : TRSignalMsg}
    (hparse : parseTrSignalMsg x.msg = some msg₀)
    (hnc : ¬ BobSessionStartCollidesOrImplicitRejects i r S g ms p x) :
    ¬ MacTagForgeryOrCollision i S g (fun u => u.AttackerKnows (runTraceMoves r ms))
      (honestSalts r ms) msg₀ (bobTrials r (runTraceMoves r ms) p x msg₀) := by
  intro ho
  apply hnc
  unfold BobSessionStartCollidesOrImplicitRejects
  rw [hparse]
  exact .inr ho

/-- Under `¬ MemoCollisionOn`, `notSpqrHeaded msg₀.mac`, `msg₀.mac ∉ plaintextTerms (runVis r₀ ms)`,
and byte equality between `msg₀.mac` and Bob's `computeMac` under `(salt₁, seed₁)`, their shapes agree. -/
theorem bs_g1_noSelfMemo_len8_of_notSpqrHeaded
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (p : PreKeyFields) (x : PreKeyRep) (msg₀ : TRSignalMsg)
    (keys : HandshakeKeys) (salt₁ seed₁ : DY.Bytes) (c' : RecvChain)
    (hbk : bobKeys r₀ p x = some keys)
    (hguard : BobTrialGuard r₀ (runTraceMoves r₀ ms) p x msg₀ = true)
    (hparse₀ : parseTrSignalMsg x.msg = some msg₀)
    (hcmk : consumeMessageKey (bobChain r₀ keys msg₀) msg₀.counter = some (seed₁, c'))
    (hsalt₁ : salt₁ ∈ honestSalts r₀ ms)
    (hmac_ne_nil : gamma interpretation S g msg₀.mac ≠ [])
    (hns : notSpqrHeaded msg₀.mac)
    (hpt : msg₀.mac ∉ plaintextTerms (runVis r₀ ms))
    (hNotMemo : ¬ MemoCollisionOn interpretation r₀ S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms) (runVis r₀ ms)
      ([x.ek, x.ct, x.msg] ++ bobTrialTerms r₀ (runTraceMoves r₀ ms) (honestSalts r₀ ms) p x msg₀) [])
    (hMacEq : gamma interpretation S g msg₀.mac =
      gamma interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey
          (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire)) :
    (gamma' interpretation S g msg₀.mac).shape =
      (gamma' interpretation S g
        (computeMac (trMsgKeys salt₁ seed₁).macKey
          (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire)).shape := by
  let cmac := computeMac (trMsgKeys salt₁ seed₁).macKey
    (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire
  have hno : notOpaqueHeaded msg₀.mac := notOpaqueHeaded_mac_of_parseTrSignalMsg hparse₀
  have hself_mac :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈ (gamma' interpretation S g msg₀.mac).memo :=
    self_mem_memo_of_notSpqrHeaded interpretation S g msg₀.mac hmac_ne_nil hns hno
  have hmac_in_msg :
      (msg₀.mac, (gamma' interpretation S g msg₀.mac).shape,
        gamma interpretation S g msg₀.mac) ∈ (gamma' interpretation S g x.msg).memo := by
    rw [parseTrSignalMsg_eq_concat hparse₀]
    exact memo_mem_of_concat_right interpretation S g _ _ hself_mac
  have hcmac_ne_nil : gamma interpretation S g cmac ≠ [] := hMacEq ▸ hmac_ne_nil
  have hself_cmac :
      (cmac, (gamma' interpretation S g cmac).shape,
        gamma interpretation S g cmac) ∈ (gamma' interpretation S g cmac).memo :=
    self_mem_memo_of_notSpqrHeaded interpretation S g cmac hcmac_ne_nil
      (notSpqrHeaded_computeMac _ _ _ _) (notOpaqueHeaded_computeMac _ _ _ _)
  have hcmac_mem : cmac ∈ bobTrialTerms r₀ (runTraceMoves r₀ ms) (honestSalts r₀ ms) p x msg₀ :=
    computeMac_mem_bobTrialTerms r₀ (runTraceMoves r₀ ms) (honestSalts r₀ ms) p x keys msg₀ seed₁ c' salt₁
      hbk hguard hcmk hsalt₁
  have hcmac_not_pt : cmac ∉ plaintextTerms (runVis r₀ ms) := by
    have h := computeMac_not_mem_ptAtoms r₀ ms [] (fun _ h => nomatch h)
      (trMsgKeys salt₁ seed₁).macKey (serializedIk (setupPublic r₀ 0))
      (serializedIk (setupPublic r₀ 2)) msg₀.wire
    rwa [List.append_nil] at h
  have hinj : assumedInjective cmac = true := by
    have hv : (cmac.view? DY.Trunc.Trunc8.SubF).isSome = true := by
      dsimp only [cmac, computeMac, DY.Trunc.trunc8, DY.Trunc.CanTrunc8.trunc8]
      rw [DY.BytesView.view_pack]; rfl
    unfold assumedInjective
    rw [hv]
    simp
  by_contra hne_sh
  apply hNotMemo
  refine ⟨(msg₀.mac, (gamma' interpretation S g msg₀.mac).shape, gamma interpretation S g msg₀.mac),
    ?_,
    (cmac, (gamma' interpretation S g cmac).shape, gamma interpretation S g cmac),
    ?_, hne_sh, Or.inr hinj, ?_, ?_, hMacEq⟩
  · rw [List.mem_flatMap]
    exact ⟨x.msg, by simp, hmac_in_msg⟩
  · rw [List.mem_append]
    refine Or.inr ?_
    rw [List.mem_flatMap]
    exact ⟨cmac, List.mem_append_right _ hcmac_mem, hself_cmac⟩
  · intro hm; simp [List.append_nil] at hm; exact False.elim (hpt hm)
  · intro hm; simp [List.append_nil] at hm; exact False.elim (hcmac_not_pt hm)

/-- Honest-send branch of pre-key MAC inversion: `msg₀.mac = Trunc.trunc8 inp₀` where `inp₀` is an
honest send's `hmac` over `trHonestWireMsg` by an available state `st_s`, matching Bob's `hmac`
shape under an honest salt `salt₁` whose `(cipherKey, macKey, iv)` bytes on `seed'` match `salt'`. -/
def BsG1bHonestSendCase
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (seed' salt' : DY.Bytes) : Prop :=
  ∃ (salt₁ : DY.Bytes),
    salt₁ ∈ honestSalts r₀ ms ∧
    ((gamma interpretation S g (trMsgKeys salt₁ seed').cipherKey =
      gamma interpretation S g (trMsgKeys salt' seed').cipherKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ seed').macKey =
      gamma interpretation S g (trMsgKeys salt' seed').macKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ seed').iv =
      gamma interpretation S g (trMsgKeys salt' seed').iv)) ∧
    ∃ (pqSalt_s seed_s myIk_s peerIk_s a_s m_s pqMsg_s : DY.Bytes)
      (ns_s pn_s : UInt32) (t_s : Nat) (st_s : TRState),
      let wire_s := trHonestWireMsg (dhPk a_s) ns_s pn_s
        (SymEnc.symEnc (trMsgKeys pqSalt_s seed_s).cipherKey (trMsgKeys pqSalt_s seed_s).iv m_s) pqMsg_s
      let inp₀ := hmac (trMsgKeys pqSalt_s seed_s).macKey
        (Concat.concat myIk_s (Concat.concat peerIk_s wire_s))
      msg₀.mac = Trunc.trunc8 inp₀ ∧
      (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms) ∧
      pqSalt_s.AttackerKnows (runTraceMoves r₀ ms) ∧
      (Concat.concat wire_s (Trunc.trunc8 inp₀)).AttackerKnows (runTraceMoves r₀ ms) ∧
      a_s = randTerm t_s 32 ∧
      st_s ∈ availableStates r₀ (runTraceMoves r₀ ms) ∧
      st_s.myIk = myIk_s ∧
      st_s.peerIk = peerIk_s ∧
      (kdfCk st_s.cks).2 = seed_s ∧
      (gamma' interpretation S g inp₀).shape =
        (gamma' interpretation S g
          (hmac (trMsgKeys salt₁ seed').macKey
            (Concat.concat (serializedIk (setupPublic r₀ 0))
              (Concat.concat (serializedIk (setupPublic r₀ 2)) msg₀.wire)))).shape

/-- Attacker-input branch of pre-key MAC inversion: `msg₀.mac = Trunc.trunc8 inp₀` with
`inp₀` attacker-known and matching Bob's `hmac` shape under an honest salt `salt₁` whose
`(cipherKey, macKey, iv)` bytes on `seed'` match `salt'`. -/
def BsG1cOwnKeyCase
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (msg₀ : TRSignalMsg) (seed' salt' : DY.Bytes) : Prop :=
  ∃ (salt₁ inp₀ : DY.Bytes),
    salt₁ ∈ honestSalts r₀ ms ∧
    ((gamma interpretation S g (trMsgKeys salt₁ seed').cipherKey =
      gamma interpretation S g (trMsgKeys salt' seed').cipherKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ seed').macKey =
      gamma interpretation S g (trMsgKeys salt' seed').macKey) ∧
     (gamma interpretation S g (trMsgKeys salt₁ seed').iv =
      gamma interpretation S g (trMsgKeys salt' seed').iv)) ∧
    msg₀.mac = Trunc.trunc8 inp₀ ∧
    inp₀.AttackerKnows (runTraceMoves r₀ ms) ∧
    (gamma' interpretation S g inp₀).shape =
      (gamma' interpretation S g
        (hmac (trMsgKeys salt₁ seed').macKey
          (Concat.concat (serializedIk (setupPublic r₀ 0))
            (Concat.concat (serializedIk (setupPublic r₀ 2)) msg₀.wire)))).shape

/-- Case split for Bob's pre-key receive MAC: under `¬ MacTagForgeryOrCollision`, `¬ MemoCollisionOn`,
and `notSpqrHeaded msg₀.mac`, either `seed'` is attacker-known, `BsG1bHonestSendCase` holds, or
`BsG1cOwnKeyCase` holds. -/
theorem bs_g1a_case_split
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (p : PreKeyFields) (x' : PreKeyRep) (msg₀ : TRSignalMsg)
    (keys' : HandshakeKeys) (st' salt' seed' : DY.Bytes) (c' : RecvChain)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hx'_msg_ak : x'.msg.AttackerKnows (runTraceMoves r₀ ms))
    (hbk' : bobKeys r₀ p x' = some keys')
    (hguard : BobTrialGuard r₀ (runTraceMoves r₀ ms) p x' msg₀ = true)
    (hparse₀ : parseTrSignalMsg x'.msg = some msg₀)
    (hcmk' : consumeMessageKey (bobChain r₀ keys' msg₀) msg₀.counter = some (seed', c'))
    (hspqr' : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys'.pqr TripleRatchet.spqrB2A)
      msg₀.pqRatchet (preKeySpqrIndex p) = some (st', salt'))
    (hmac_ne_nil : gamma interpretation S g msg₀.mac ≠ [])
    (hns_mac : notSpqrHeaded msg₀.mac)
    (hpt_mac : msg₀.mac ∉ plaintextTerms (runVis r₀ ms))
    (hNotMemo : ¬ MemoCollisionOn interpretation r₀ S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (runTraceMoves r₀ ms) (runVis r₀ ms)
      ([x'.ek, x'.ct, x'.msg] ++ bobTrialTerms r₀ (runTraceMoves r₀ ms) (honestSalts r₀ ms) p x' msg₀) [])
    (hNotOwn : ¬ MacTagForgeryOrCollision interpretation S g
      (fun u => u.AttackerKnows (runTraceMoves r₀ ms)) (honestSalts r₀ ms) msg₀
      (bobTrials r₀ (runTraceMoves r₀ ms) p x' msg₀))
    (hMacBytes : gamma interpretation S g
      (computeMac (trMsgKeys salt' seed').macKey
        (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire) =
      gamma interpretation S g msg₀.mac) :
    seed'.AttackerKnows (runTraceMoves r₀ ms) ∨
    BsG1bHonestSendCase interpretation r₀ S g ms msg₀ seed' salt' ∨
    BsG1cOwnKeyCase interpretation r₀ S g ms msg₀ seed' salt' := by
  by_cases hSeedKnows : seed'.AttackerKnows (runTraceMoves r₀ ms)
  · exact Or.inl hSeedKnows
  · obtain ⟨salt₁, hsalt₁, hck₁_eq, hmk₁_eq, hiv₁_eq⟩ :=
      exists_honestSalt_of_not_bobOwnSaltMacCollision hbk' hguard hcmk' hSeedKnows hspqr'
        hMacBytes hNotOwn
    have hcmac_eq : gamma interpretation S g
        (computeMac (trMsgKeys salt₁ seed').macKey
          (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire) =
        gamma interpretation S g
          (computeMac (trMsgKeys salt' seed').macKey
            (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire) :=
      gamma_computeMac_congr_macKey interpretation S g _ _ _ _ _ hmk₁_eq
    have hMacEq : gamma interpretation S g msg₀.mac =
        gamma interpretation S g
          (computeMac (trMsgKeys salt₁ seed').macKey
            (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire) :=
      hMacBytes.symm.trans hcmac_eq.symm
    have hShMac : (gamma' interpretation S g msg₀.mac).shape =
        (gamma' interpretation S g
          (computeMac (trMsgKeys salt₁ seed').macKey
            (serializedIk (setupPublic r₀ 0)) (serializedIk (setupPublic r₀ 2)) msg₀.wire)).shape :=
      bs_g1_noSelfMemo_len8_of_notSpqrHeaded interpretation r₀ S g ms p x' msg₀ keys' salt₁ seed' c'
        hbk' hguard hparse₀ hcmk' hsalt₁ hmac_ne_nil hns_mac hpt_mac hNotMemo hMacEq
    let rhsHmac := hmac (trMsgKeys salt₁ seed').macKey
      (Concat.concat (serializedIk (setupPublic r₀ 0))
        (Concat.concat (serializedIk (setupPublic r₀ 2)) msg₀.wire))
    have hview : DY.Bytes.view? (gamma' interpretation S g msg₀.mac).shape DY.Trunc.Trunc8.SubF =
        some { input := (gamma' interpretation S g rhsHmac).shape } := by
      rw [hShMac]
      unfold computeMac
      rw [shape_trunc8_tr]
      exact DY.BytesView.view_pack (SubF := DY.Trunc.Trunc8.SubF) _
    obtain ⟨inp₀, hmac_eq, hshape_eq⟩ :=
      (view?_trunc8_shape_eq_some_iff interpretation S g msg₀.mac
        (gamma' interpretation S g rhsHmac).shape).mp hview
    have hmac₀_knows : msg₀.mac.AttackerKnows (runTraceMoves r₀ ms) :=
      attackerKnows_mac_of_parseTrSignalMsg hx'_msg_ak hparse₀
    have hmac_knows : (Trunc.trunc8 inp₀).AttackerKnows (runTraceMoves r₀ ms) := by
      rwa [hmac_eq] at hmac₀_knows
    rcases macKdfSafe_c_trunc8_inv_strong r₀ ms inp₀ hreach hmac_knows with
      hinp_knows | ⟨pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, ns_s, pn_s, m_s, pqMsg_s, t_s, st_s,
        hinp_eq, hpqSalt_ak, hmsg_s_ak, ha_eq, hst_s, hmyIk, hpeerIk, hseed_s⟩
    · exact Or.inr (Or.inr ⟨salt₁, inp₀, hsalt₁, ⟨hck₁_eq, hmk₁_eq, hiv₁_eq⟩,
        hmac_eq, hinp_knows, hshape_eq⟩)
    · subst hinp_eq
      exact Or.inr (Or.inl ⟨salt₁, hsalt₁, ⟨hck₁_eq, hmk₁_eq, hiv₁_eq⟩,
        pqSalt_s, seed_s, myIk_s, peerIk_s, a_s, m_s, pqMsg_s, ns_s, pn_s, t_s, st_s,
        hmac_eq, hmac_knows, hpqSalt_ak, hmsg_s_ak, ha_eq, hst_s, hmyIk, hpeerIk, hseed_s,
        hshape_eq⟩)

/-! ## Bob's pre-key spine and opposite-parity equality -/

/-- KEM shared-secret term in `bobKeys r p x`: decapsulation if `kemDecap` succeeds, or the
implicit-rejection `kemRejKey` fallback. -/
def bobKemShare (r : ProtocolSetup) (x : PreKeyRep) : DY.Bytes :=
  (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD
    (DY.PQKem.kemRejKey (setupSecret r 4) x.ct)

theorem bobAgreement_eq_some (r : ProtocolSetup) (x : PreKeyRep) (opk : Option DY.Bytes) :
    DY.Libsignal.PQXDH.bobAgreement (setupSecret r 1) (setupSecret r 2) (setupSecret r 4) opk
      (setupPublic r 0) x.ek x.ct = some (bobKeysOf r x opk) := rfl

theorem kemLeaf_bobKemShare (r : ProtocolSetup) (x : PreKeyRep) :
    ShapeModKem.KemLeaf (bobKemShare r x) := by
  unfold bobKemShare
  cases hd : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct) with
  | none =>
    exact .inr ⟨setupSecret r 4, x.ct, rfl⟩
  | some ss =>
    obtain ⟨e, _, rfl⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hd
    exact .inl ⟨DY.PQKem.kemPk (setupSecret r 4), e, rfl⟩

/-- The PQXDH input key material for Bob's pre-key handshake on `(r, p, x)`. -/
def BobPreKeyIkm (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep) (ikm : DY.Bytes) : Prop :=
  ∃ opk, OpkSel r p opk ∧
    ikm = DY.Libsignal.PQXDH.pqxdhIkm
      (DY.Libsignal.PQXDH.agree (setupPublic r 0) (setupSecret r 2))
      (DY.Libsignal.PQXDH.agree x.ek (setupSecret r 1))
      (DY.Libsignal.PQXDH.agree x.ek (setupSecret r 2))
      (opk.map (DY.Libsignal.PQXDH.agree x.ek ·))
      (bobKemShare r x)

theorem bobKeys_eq_some_iff_bobPreKeyIkm (r : ProtocolSetup) (p : PreKeyFields) (x : PreKeyRep)
    (keys : DY.Libsignal.PQXDH.HandshakeKeys)
    (hk : bobKeys r p x = some keys) :
    ∃ ikm, BobPreKeyIkm r p x ikm ∧ keys = DY.Libsignal.PQXDH.pqxdhKdf ikm := by
  obtain ⟨opk, hsel, rfl⟩ := bobKeys_unpack r p x keys hk
  exact ⟨_, ⟨opk, hsel, rfl⟩, rfl⟩

/-- Base-IKM predicate combining handshake IKMs logged on `runTraceMoves r ms` with Bob's
in-progress pre-key handshake IKM at role `true`. -/
def LoggedOrBobIkmRk (r : ProtocolSetup) (ms : List Move) (p : PreKeyFields) (x : PreKeyRep)
    (c : Bool) (ikm : DY.Bytes) : Prop :=
  LoggedIkmRk (runTraceMoves r ms) c ikm ∨ (c = true ∧ BobPreKeyIkm r p x ikm)

private theorem pqSkAt_of_runTrace_at? {r : ProtocolSetup} {ms : List Move} {j : Nat}
    {me : Participant} {st : DY.Libsignal.PQXDH.PQXDHState}
    (h : (runTraceMoves r ms).at? j = some (TR.StE me st)) :
    PQSkAt (runTraceMoves r ms) j st := by
  have htr := traceOkR_runTrace r ms
  change ((runTraceMoves r ms).at? j : Option Ik.IkPQStEntry) = some ⟨⟨me, st⟩⟩ at h
  unfold DY.Trace.at? at h
  split at h
  · next hj => exact (htr j hj).2 ⟨⟨me, st⟩⟩ h
  · cases h

private theorem ikAt_of_runTrace_at? {r : ProtocolSetup} {ms : List Move} {j : Nat}
    {me : Participant} {sk : DY.Bytes}
    (h : (runTraceMoves r ms).at? j = some (TR.StE me { kind := .identity, sk := sk })) :
    ∃ t, t < j ∧ sk = randTerm t 32 ∧ IkAt (runTraceMoves r ms) t :=
  pqSkAt_of_runTrace_at? h

private theorem spkAt_of_runTrace_at? {r : ProtocolSetup} {ms : List Move} {j : Nat}
    {me : Participant} {sk : DY.Bytes}
    (h : (runTraceMoves r ms).at? j = some (TR.StE me { kind := .signedPrekey, sk := sk })) :
    ∃ t, t < j ∧ sk = randTerm t 32 ∧ SpkAt (runTraceMoves r ms) t :=
  pqSkAt_of_runTrace_at? h

private theorem opkAt_of_runTrace_at? {r : ProtocolSetup} {ms : List Move} {j : Nat}
    {me : Participant} {sk : DY.Bytes}
    (h : (runTraceMoves r ms).at? j = some (TR.StE me { kind := .oneTimePrekey, sk := sk })) :
    ∃ t, t < j ∧ sk = randTerm t 32 ∧ OpkAt (runTraceMoves r ms) t :=
  pqSkAt_of_runTrace_at? h

private theorem agree_eq_dh_x25519Key (pk : DY.Bytes) {sk : DY.Bytes} {t : Nat}
    (h : sk = randTerm t 32) :
    DY.Libsignal.PQXDH.agree pk sk =
      dh (DY.X25519.normalizeX25519Key pk) (randTerm t 32) := by
  subst h; rfl

private theorem topDhSecret_pqxdh_of_agree (ikA : DY.Bytes) {sk b e : DY.Bytes}
    {d : Option DY.Bytes} {ss : DY.Bytes} {t : Nat} (h : sk = randTerm t 32) :
    TopDhSecret (DY.Libsignal.PQXDH.pqxdhKdf
      (DY.Libsignal.PQXDH.pqxdhIkm (DY.Libsignal.PQXDH.agree ikA sk) b e d ss)).rk
      (DY.X25519.normalizeX25519Key ikA) t := by
  subst h
  exact topDhSecret_pqxdh (pk' := DY.X25519.normalizeX25519Key ikA) (t := t)

private theorem createChain_snd_eq (rk pk : DY.Bytes) {sk : DY.Bytes} {t : Nat}
    (h : sk = randTerm t 32) :
    (createChain rk pk sk).2 =
      (kdfRk rk (dh (DY.X25519.normalizeX25519Key pk) (randTerm t 32))).2 := by
  subst h; rfl

private theorem bobChain_chainKey_eq (r : ProtocolSetup) (keys : HandshakeKeys) (msg₀ : TRSignalMsg) :
    (bobChain r keys msg₀).chainKey =
      (createChain keys.rk msg₀.ratchetKey (setupSecret r 2)).2 :=
  rfl

private theorem at?_some_of_le {E : Type} [ExecTraceTypes.Has E] {t T : ExecTrace}
    (hle : t ≤ T) {j : Nat} {x : E} (h : (t.at? j : Option E) = some x) :
    (T.at? j : Option E) = some x := by
  by_cases hj : j < t.length
  · rw [← h, at?_of_le hle hj]
  · simp [Trace.at?, hj] at h

local macro "peel_setup_at" : tactic => `(tactic|
  (simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
   repeat (first
     | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Trace.append, Trace.length])
     | exact TR.at?_append_eq _ _ rfl)))

theorem runTrace_at?_9 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 9 = some (TR.StE r.bob { kind := .identity, sk := setupSecret r 1 }) := by
  refine at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [(TR.setupSecret_eq r hne).2.1, TR.setupTrace_eq r hne]
  cases r.withOpk <;> (
    simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat (first
      | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

theorem runTrace_at?_13 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 13 = some (TR.StE r.bob { kind := .signedPrekey, sk := setupSecret r 2 }) := by
  refine at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [(TR.setupSecret_eq r hne).2.2.1, TR.setupTrace_eq r hne]
  cases r.withOpk <;> (
    simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat (first
      | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

theorem runTrace_at?_24 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move)
    (hopk : r.withOpk = true) :
    (runTraceMoves r ms).at? 24 = some (TR.StE r.bob { kind := .oneTimePrekey, sk := setupSecret r 6 }) := by
  refine at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [(TR.setupSecret_eq r hne).2.2.2.2 hopk, TR.setupTrace_eq r hne, hopk]
  simp only [↓reduceIte, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
  repeat (first
    | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
    | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]))

theorem runTrace_at?_2 (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (runTraceMoves r ms).at? 2 = some (TR.NetE (setupPublic r 0)) := by
  have h0 : setupPublic r 0 = DY.DiffieHellman.dhPk (randTerm 0 32) := by
    rw [(TR.setupPublic_eq r hne).1, (TR.setupSecret_eq r hne).1]
  rw [h0]; refine at?_some_of_le (setupTrace_le_runTrace r ms) ?_
  rw [TR.setupTrace_eq r hne]
  cases r.withOpk <;> (
    simp only [↓reduceIte, Bool.false_eq_true, TR.setupTr5, TR.setupTr4, TR.setupTr3, TR.setupTr2, TR.setupTr1]
    repeat (first
      | (rw [TR.at?_append_of_lt _ _ ?hlt]; case hlt => simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])
      | exact TR.at?_append_eq _ _ (by simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2])))

theorem setupPublic_0_attackerKnows (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (ms : List Move) :
    (setupPublic r 0).AttackerKnows (runTraceMoves r ms) :=
  Symbolic.Swarm.CREF.TR.attackerKnows_of_at?_network (runTrace_at?_2 r hne ms)

theorem bobPreKeyIkm_roleHoles {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    {p : PreKeyFields} {x : PreKeyRep} {m : DY.Bytes}
    (hm : BobPreKeyIkm r p x m) :
    ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
      m = DY.Libsignal.PQXDH.pqxdhIkm a b e d ss ∧
      IkmRoleHoles (IkAt (runTraceMoves r ms)) (SpkAt (runTraceMoves r ms))
        (OpkAt (runTraceMoves r ms)) (EkAt (runTraceMoves r ms)) true a b e d ∧
      ShapeModKem.KemLeaf ss := by
  obtain ⟨opk, hsel, rfl⟩ := hm
  obtain ⟨tᵢ, _, hik, hikAt⟩ := ikAt_of_runTrace_at? (runTrace_at?_9 r hne ms)
  obtain ⟨tₛ, _, hspk, hspkAt⟩ := spkAt_of_runTrace_at? (runTrace_at?_13 r hne ms)
  refine ⟨_, _, _, opk.map (DY.Libsignal.PQXDH.agree x.ek ·), bobKemShare r x, rfl, ?_,
    kemLeaf_bobKemShare r x⟩
  refine ⟨⟨DY.X25519.normalizeX25519Key (setupPublic r 0), tₛ, agree_eq_dh_x25519Key _ hspk, hspkAt⟩,
    ⟨DY.X25519.normalizeX25519Key x.ek, tᵢ, agree_eq_dh_x25519Key _ hik, hikAt⟩,
    ⟨DY.X25519.normalizeX25519Key x.ek, tₛ, agree_eq_dh_x25519Key _ hspk, hspkAt⟩, fun v hv => ?_⟩
  rcases hsel with ⟨_, rfl⟩ | ⟨hw, _, rfl⟩
  · cases hv
  · injection hv with hv; subst hv
    obtain ⟨tₒ, _, hopk, hopkAt⟩ := opkAt_of_runTrace_at? (runTrace_at?_24 r hne ms hw)
    exact ⟨DY.X25519.normalizeX25519Key x.ek, tₒ, agree_eq_dh_x25519Key _ hopk, hopkAt⟩

theorem loggedOrBobIkmRk_roleHoles {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    {p : PreKeyFields} {x : PreKeyRep} {c : Bool} {m : DY.Bytes}
    (h : LoggedOrBobIkmRk r ms p x c m) :
    ∃ (a b e : DY.Bytes) (d : Option DY.Bytes) (ss : DY.Bytes),
      m = DY.Libsignal.PQXDH.pqxdhIkm a b e d ss ∧
      IkmRoleHoles (IkAt (runTraceMoves r ms)) (SpkAt (runTraceMoves r ms))
        (OpkAt (runTraceMoves r ms)) (EkAt (runTraceMoves r ms)) c a b e d ∧
      ShapeModKem.KemLeaf ss := by
  rcases h with hlog | ⟨rfl, hbob⟩
  · exact loggedIkmRk_roleHoles hlog
  · exact bobPreKeyIkm_roleHoles hne ms hbob

/-- Bob's pre-key receive seed `seed'` satisfies `SpineRk (LoggedOrBobIkmRk r ms p x) false seed'`. -/
theorem spineRk_bobSeed {r : ProtocolSetup} (hne : r.alice ≠ r.bob) (ms : List Move)
    {p : PreKeyFields} {x : PreKeyRep} {keys : DY.Libsignal.PQXDH.HandshakeKeys}
    {msg₀ : TRSignalMsg} {seed' : DY.Bytes} {c' : RecvChain}
    (hkeys : bobKeys r p x = some keys)
    (hcmk : consumeMessageKey (bobChain r keys msg₀) msg₀.counter = some (seed', c')) :
    SpineRk (LoggedOrBobIkmRk r ms p x) false seed' := by
  obtain ⟨ikm, hikm, hkeys_eq⟩ := bobKeys_eq_some_iff_bobPreKeyIkm r p x keys hkeys
  obtain ⟨opk, hsel, hikm_eq⟩ := hikm
  obtain ⟨tₛ, _, hspk, _⟩ := spkAt_of_runTrace_at? (runTrace_at?_13 r hne ms)
  have hB : LoggedOrBobIkmRk r ms p x true ikm := Or.inr ⟨rfl, opk, hsel, hikm_eq⟩
  have hrk0 : SpineRk (LoggedOrBobIkmRk r ms p x) true keys.rk := by
    rw [hkeys_eq]; exact .hsRk hB
  have htop0 : TopDhSecret keys.rk (DY.X25519.normalizeX25519Key (setupPublic r 0)) tₛ := by
    rw [hkeys_eq, hikm_eq]
    exact topDhSecret_pqxdh_of_agree (setupPublic r 0) hspk
  have hh : RkHole true keys.rk
      (dh (DY.X25519.normalizeX25519Key msg₀.ratchetKey) (randTerm tₛ 32)) :=
    rkHole_true_intro htop0
  have hck : SpineRk (LoggedOrBobIkmRk r ms p x) false (bobChain r keys msg₀).chainKey := by
    rw [bobChain_chainKey_eq r keys msg₀, createChain_snd_eq _ _ hspk]
    exact .rkStep2 hrk0 hh
  exact (spineRk_consumeMessageKey hck hcmk).1

unseal DY.Bytes in
private theorem kemLeaf_ne_concat_raw {ss l r : DY.Bytes} (hss : ShapeModKem.KemLeaf ss) :
    ss ≠ Concat.concat l r := by
  intro h
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.Concat.Concat.SubF) h
  have hsome : DY.Bytes.view? (Concat.concat l r) DY.Concat.Concat.SubF =
      some { lhs := l, rhs := r } :=
    DY.BytesView.view_pack (SubF := DY.Concat.Concat.SubF) { lhs := l, rhs := r }
  rcases hss with ⟨pk, e, rfl⟩ | ⟨sk, ct, rfl⟩
  · rw [Stage1Kyber.kemEncap_snd_eq_pack] at hv
    have hnone : DY.Bytes.view?
        (({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack)
        DY.Concat.Concat.SubF = none :=
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _
    rw [hnone, hsome] at hv
    cases hv
  · rw [(Stage1Kyber.view?_kemRejKey_disjoint sk ct).1, hsome] at hv
    cases hv

unseal DY.Bytes in
private theorem kemRejKey_ne_kemEncap_snd (sk ct pk e : DY.Bytes) :
    DY.PQKem.kemRejKey sk ct ≠ (DY.PQKem.kemEncap pk e).2 := by
  intro h
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.SharedSecret.SubF) h
  rw [(Stage1Kyber.view?_kemRejKey_disjoint sk ct).2.2.2.2.2.2.2.2.2.1,
      Stage1Kyber.kemEncap_snd_eq_pack,
      DY.BytesView.view_pack (SubF := DY.PQKem.SharedSecret.SubF) { pk := pk, entropy := e }] at hv
  cases hv

private theorem pqxdhIkm_kemLeaf_eq {a₁ b₁ e₁ a₂ b₂ e₂ ss₁ ss₂ : DY.Bytes}
    {d₁ d₂ : Option DY.Bytes}
    (hss₁ : ShapeModKem.KemLeaf ss₁) (hss₂ : ShapeModKem.KemLeaf ss₂)
    (h : pqxdhIkm a₁ b₁ e₁ d₁ ss₁ = pqxdhIkm a₂ b₂ e₂ d₂ ss₂) :
    ss₁ = ss₂ := by
  unfold pqxdhIkm at h
  have h' := (concat_injective (concat_injective (concat_injective
    (concat_injective h).2).2).2).2
  cases d₁ <;> cases d₂ <;> dsimp only at h'
  · exact h'
  · exact absurd h' (kemLeaf_ne_concat_raw hss₁)
  · exact absurd h'.symm (kemLeaf_ne_concat_raw hss₂)
  · exact (concat_injective h').2

private theorem pqxdhKdf_rk_inj {m₁ m₂ : DY.Bytes}
    (h : (pqxdhKdf m₁).rk = (pqxdhKdf m₂).rk) : m₁ = m₂ := by
  unfold pqxdhKdf at h
  dsimp only at h
  exact (kdfExtract_injective (kdfExtract_injective h).1).2

private theorem aliceDone_kemSS_of_loggedIkmRk
    {T : ExecTrace} (hinv : Symbolic.Swarm.COMPOSED.CompInv.SpqrInv T)
    {ikm : DY.Bytes} (hlog : LoggedIkmRk T false ikm) :
    ∃ (t : Nat) (a₀ b₀ : Participant) (ikA₀ ikB₀ spk₀ pqpk₀ : DY.Bytes)
      (opk₀ : Option DY.Bytes) (ek₀ ct₀ : DY.Bytes) (keys₀ : HandshakeKeys)
      (a₁ b₁ e₁ : DY.Bytes) (d₁ : Option DY.Bytes),
      Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t ∧
      T.EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀)
        (t + 5) ∧
      IkmRoleHoles (IkAt T) (SpkAt T) (OpkAt T) (EkAt T) false a₁ b₁ e₁ d₁ ∧
      ikm = pqxdhIkm a₁ b₁ e₁ d₁ (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2 := by
  unfold LoggedIkmRk LoggedPQEv at hlog
  rcases hlog with ⟨ev, ⟨j, e, hat, rfl⟩, hdone⟩
  cases hev : e.ev
  all_goals rw [hev] at hdone
  case AliceDone a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀ =>
    dsimp only [DoneIkmRk, CtKeysIkmR] at hdone
    obtain ⟨pk', ent', a₁, b₁, e₁, d₁, _, hikm₁, hkeys₁, hroles₁⟩ := hdone
    have hevA : T.EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀) j := by
      rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
      cases e; dsimp only at hev; subst hev; exact hat
    obtain ⟨t, sA, rfl, hs, -, -, -, hag, -⟩ := hinv.aliceDone _ _ _ _ _ _ _ _ _ _ _ hevA
    have hkeys₂ : ∃ (a₂ b₂ e₂ : DY.Bytes) (d₂ : Option DY.Bytes),
        keys₀ = pqxdhKdf (pqxdhIkm a₂ b₂ e₂ d₂ (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2) := by
      rcases hk : DY.PQKem.kemEncap pqpk₀
          (Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd (t + 1) 32) with ⟨c₀, s₀⟩
      unfold DY.Libsignal.PQXDH.aliceAgreement at hag
      rw [hk] at hag
      simp only [Prod.mk.injEq] at hag
      have hrnd : Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd (t + 1) 32 = randTerm (t + 1) 32 := rfl
      rw [hrnd] at hk
      have hs₀ : s₀ = (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2 := by rw [hk]
      exact ⟨_, _, _, _, hs₀ ▸ hag.2⟩
    obtain ⟨a₂, b₂, e₂, d₂, hkeys₂⟩ := hkeys₂
    have hikm_eq : pqxdhIkm a₁ b₁ e₁ d₁ (DY.PQKem.kemEncap pk' ent').2 =
        pqxdhIkm a₂ b₂ e₂ d₂ (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2 :=
      pqxdhKdf_rk_inj ((congrArg HandshakeKeys.rk (hikm₁ ▸ hkeys₁)).symm.trans
        (congrArg HandshakeKeys.rk hkeys₂))
    have hss_eq : (DY.PQKem.kemEncap pk' ent').2 =
        (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2 :=
      pqxdhIkm_kemLeaf_eq (.inl ⟨_, _, rfl⟩) (.inl ⟨_, _, rfl⟩) hikm_eq
    exact ⟨t, a₀, b₀, ikA₀, ikB₀, spk₀, pqpk₀, opk₀, ek₀, ct₀, keys₀, a₁, b₁, e₁, d₁,
      hs, hevA, hroles₁, hss_eq ▸ hikm₁⟩
  all_goals cases hdone

private theorem bobSide_kemSS_of_loggedOrBobIkmRk
    {r : ProtocolSetup} (hne : r.alice ≠ r.bob) {ms : List Move} {p : PreKeyFields} {x : PreKeyRep}
    (hinv : Symbolic.Swarm.COMPOSED.CompInv.SpqrInv (runTraceMoves r ms))
    (hx_ct_ak : x.ct.AttackerKnows (runTraceMoves r ms))
    (hbob_ct_ak : ∀ b a ikB ikA spk pqpk opk ek ct keys idx,
      (runTraceMoves r ms).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) idx →
      ct.AttackerKnows (runTraceMoves r ms))
    {ikm : DY.Bytes} (hB : LoggedOrBobIkmRk r ms p x true ikm) :
    ∃ (a₂ b₂ e₂ : DY.Bytes) (d₂ : Option DY.Bytes) (ss₂ : DY.Bytes),
      IkmRoleHoles (IkAt (runTraceMoves r ms)) (SpkAt (runTraceMoves r ms))
        (OpkAt (runTraceMoves r ms)) (EkAt (runTraceMoves r ms)) true a₂ b₂ e₂ d₂ ∧
      ShapeModKem.KemLeaf ss₂ ∧
      ikm = pqxdhIkm a₂ b₂ e₂ d₂ ss₂ ∧
      ((∃ pk₂ ent₂, ss₂ = (DY.PQKem.kemEncap pk₂ ent₂).2 ∧
          (ent₂.AttackerKnows (runTraceMoves r ms) ∨
            (DY.PQKem.kemEncap pk₂ ent₂).1.AttackerKnows (runTraceMoves r ms))) ∨
        (∃ sk₂ ct₂, ss₂ = DY.PQKem.kemRejKey sk₂ ct₂)) := by
  rcases hB with hlog | ⟨_, hbob⟩
  · unfold LoggedIkmRk LoggedPQEv at hlog
    rcases hlog with ⟨ev, ⟨j, e, hat, rfl⟩, hdone⟩
    cases hev : e.ev
    all_goals rw [hev] at hdone
    case BobDone b₁ a₁ ikB₁ ikA₁ spk₁ pqpk₁ opk₁ ek₁ ct₁ keys₁ =>
      dsimp only [DoneIkmRk, CtKeysIkmR] at hdone
      obtain ⟨ss₂, a₂, b₂, e₂, d₂, hleaf₂, hikm₂, hkeys₁, hroles₂⟩ := hdone
      have hevB : (runTraceMoves r ms).EventLoggedAt
          (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b₁ a₁ ikB₁ ikA₁ spk₁ pqpk₁ opk₁ ek₁ ct₁ keys₁) j := by
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
        cases e; dsimp only at hev; subst hev; exact hat
      obtain ⟨sB, sS, pqsk, o, ss₀, -, -, -, -, -, -, -, -, -, hss₀, hkeys₀, -⟩ :=
        hinv.bobDone _ _ _ _ _ _ _ _ _ _ j hevB
      rw [hss₀] at hkeys₀
      have hikm_eq := pqxdhKdf_rk_inj
        ((congrArg HandshakeKeys.rk (hikm₂ ▸ hkeys₁)).symm.trans (congrArg HandshakeKeys.rk hkeys₀))
      cases hd : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap pqsk ct₁) with
      | none =>
        rw [hd] at hikm_eq
        dsimp only [Option.getD] at hikm_eq
        have hss₂_eq := pqxdhIkm_kemLeaf_eq hleaf₂ (.inr ⟨pqsk, ct₁, rfl⟩) hikm_eq
        exact ⟨a₂, b₂, e₂, d₂, ss₂, hroles₂, hleaf₂, hikm₂, .inr ⟨pqsk, ct₁, hss₂_eq⟩⟩
      | some s =>
        obtain ⟨ent₂, hct_eq, hs_eq⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hd
        rw [hd] at hikm_eq
        dsimp only [Option.getD] at hikm_eq
        rw [hs_eq] at hikm_eq
        have hss₂_eq := pqxdhIkm_kemLeaf_eq hleaf₂ (.inl ⟨_, _, rfl⟩) hikm_eq
        have hct_ak := hbob_ct_ak _ _ _ _ _ _ _ _ _ _ j hevB
        rw [hct_eq] at hct_ak
        exact ⟨a₂, b₂, e₂, d₂, ss₂, hroles₂, hleaf₂, hikm₂,
          .inl ⟨DY.PQKem.kemPk pqsk, ent₂, hss₂_eq, Or.inr hct_ak⟩⟩
    all_goals cases hdone
  · obtain ⟨a₂, b₂, e₂, d₂, ss₂, hikm₂, hroles₂, hleaf₂⟩ := bobPreKeyIkm_roleHoles hne ms hbob
    obtain ⟨opk, _, hikm_bob⟩ := hbob
    have hss₂_eq : ss₂ = bobKemShare r x :=
      pqxdhIkm_kemLeaf_eq hleaf₂ (kemLeaf_bobKemShare r x) (hikm₂.symm.trans hikm_bob)
    subst hss₂_eq
    cases hd : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct) with
    | none =>
      exact ⟨a₂, b₂, e₂, d₂, bobKemShare r x, hroles₂, kemLeaf_bobKemShare r x, hikm₂,
        .inr ⟨setupSecret r 4, x.ct, by unfold bobKemShare; rw [hd]; rfl⟩⟩
    | some ss' =>
      obtain ⟨ent₂, hct_eq, hss'_eq⟩ := Stage1Kyber.errToOption_kemDecap_eq_some_iff.mp hd
      have hct_ak := hx_ct_ak
      rw [hct_eq] at hct_ak
      exact ⟨a₂, b₂, e₂, d₂, bobKemShare r x, hroles₂, kemLeaf_bobKemShare r x, hikm₂,
        .inl ⟨DY.PQKem.kemPk (setupSecret r 4), ent₂,
          by unfold bobKemShare; rw [hd, Option.getD, hss'_eq], Or.inr hct_ak⟩⟩

private theorem aliceBob_kemLeaf_eq
    (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {T : ExecTrace}
    (hinv : Symbolic.Swarm.COMPOSED.CompInv.SpqrInv T)
    (henc_inv : ∀ pk e, (DY.PQKem.kemEncap pk e).1.AttackerKnows T →
      e.AttackerKnows T ∨
      ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        T.EventLoggedAt
          (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        pk = pqpk ∧ e = randTerm (t + 1) 32)
    {t : Nat} {a₀ b₀ : Participant} {ikA₀ ikB₀ spk₀ pqpk₀ : DY.Bytes}
    {opk₀ : Option DY.Bytes} {ek₀ ct₀ : DY.Bytes} {keys₀ : HandshakeKeys}
    {ss₂ : DY.Bytes}
    (hs : Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t)
    (hevA : T.EventLoggedAt
      (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a₀ b₀ ikA₀ ikB₀ spk₀ pqpk₀ opk₀ ek₀ ct₀ keys₀)
      (t + 5))
    (h32 : (gamma i S g (randTerm (t + 1) 32)).length = 32)
    (hB_ss : (∃ pk₂ ent₂, ss₂ = (DY.PQKem.kemEncap pk₂ ent₂).2 ∧
        (ent₂.AttackerKnows T ∨ (DY.PQKem.kemEncap pk₂ ent₂).1.AttackerKnows T)) ∨
      (∃ sk₂ ct₂, ss₂ = DY.PQKem.kemRejKey sk₂ ct₂))
    (hsh : (gamma' i S g (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2).shape =
      (gamma' i S g ss₂).shape) :
    (DY.PQKem.kemEncap pqpk₀ (randTerm (t + 1) 32)).2 = ss₂ := by
  obtain ⟨pk₂', e₂', hu_eq, _, _, he_sh⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 i S g h32 hsh.symm
  rcases hB_ss with ⟨pk₂, ent₂, rfl, hB_ak⟩ | ⟨sk₂, ct₂, rfl⟩
  · obtain ⟨_, rfl⟩ := Stage1Kyber.kemEncap_snd_inj hu_eq
    have hsz : (32 : Nat) ≠ 0 := by decide
    rw [(Stage1Kyber.shape_eq_randTerm_iff i S g (randTerm (t + 1) 32) hsz).mpr rfl] at he_sh
    have hent_eq : ent₂ = randTerm (t + 1) 32 :=
      (Stage1Kyber.shape_eq_randTerm_iff i S g ent₂ hsz).mp he_sh
    subst hent_eq
    have hnot_pub := Symbolic.Swarm.COMPOSED.CompInv.not_pub_coins_of_spqrInv hinv hs
    have hrnd : Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd (t + 1) 32 = randTerm (t + 1) 32 := rfl
    rw [hrnd] at hnot_pub
    rcases hB_ak with hent_ak | hct_ak
    · exact absurd (Symbolic.Swarm.COMPOSED.CompInv.CompPubInv.Pub.of_attackerKnows hinv hent_ak) hnot_pub
    · rcases henc_inv pk₂ (randTerm (t + 1) 32) hct_ak with hent_ak |
        ⟨t', a', b', ikA', ikB', spk', pqpk', opk', ek', ct', keys', hevA', rfl, hr_eq⟩
      · exact absurd (Symbolic.Swarm.COMPOSED.CompInv.CompPubInv.Pub.of_attackerKnows hinv hent_ak) hnot_pub
      · have ht_eq : t = t' := by
          have := randTerm32_injective hr_eq
          omega
        subst ht_eq
        have hev_eq := Symbolic.Swarm.COMPOSED.CompInv.CompPresBob.evAt_unique hevA hevA'
        injection hev_eq with _ _ _ _ _ hpq _ _ _ _
        rw [hpq]
  · exact absurd hu_eq (kemRejKey_ne_kemEncap_snd sk₂ ct₂ pk₂' e₂')

private theorem loggedOrBobIkmRk_kemSS_eq
    (i : ExternInterpretation) (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (p : PreKeyFields) (x : PreKeyRep)
    (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability)
    (hx_ct_ak : x.ct.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r ms) t →
      (gamma i S g (randTerm (t + 1) 32)).length = 32)
    (henc_inv : ∀ pk e, (DY.PQKem.kemEncap pk e).1.AttackerKnows (runTraceMoves r ms) →
      e.AttackerKnows (runTraceMoves r ms) ∨
      ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        (runTraceMoves r ms).EventLoggedAt
          (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        pk = pqpk ∧ e = randTerm (t + 1) 32)
    (hbob_ct_ak : ∀ b a ikB ikA spk pqpk opk ek ct keys idx,
      (runTraceMoves r ms).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) idx →
      ct.AttackerKnows (runTraceMoves r ms))
    {a b e : DY.Bytes} {d : Option DY.Bytes} {ss₁ ss₂ : DY.Bytes}
    (hA : LoggedOrBobIkmRk r ms p x false (pqxdhIkm a b e d ss₁))
    (hB : LoggedOrBobIkmRk r ms p x true (pqxdhIkm a b e d ss₂))
    (hsh : (gamma' i S g ss₁).shape = (gamma' i S g ss₂).shape) :
    ss₁ = ss₂ := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach
  have hA_log : LoggedIkmRk (runTraceMoves r ms) false (pqxdhIkm a b e d ss₁) := by
    rcases hA with hlog | ⟨hfalse, _⟩
    · exact hlog
    · cases hfalse
  obtain ⟨t, a₀, b₀, ikA₀, ikB₀, spk₀, pqpk₀, opk₀, ek₀, ct₀, keys₀, a₁, b₁, e₁, d₁,
    hs, hevA, hroles₁, hikm₁⟩ := aliceDone_kemSS_of_loggedIkmRk hinv hA_log
  obtain ⟨a₂, b₂, e₂, d₂, ss₂', hroles₂, hleaf₂, hikm₂, hB_ss⟩ :=
    bobSide_kemSS_of_loggedOrBobIkmRk hne hinv hx_ct_ak hbob_ct_ak hB
  unfold pqxdhIkm at hikm₁ hikm₂
  have htail₁ := (concat_injective (concat_injective (concat_injective
    (concat_injective hikm₁).2).2).2).2
  have htail₂ := (concat_injective (concat_injective (concat_injective
    (concat_injective hikm₂).2).2).2).2
  cases d with
  | some v =>
    cases d₁ with
    | none =>
      dsimp only at htail₁
      exact absurd htail₁.symm (kemLeaf_ne_concat_raw (.inl ⟨_, _, rfl⟩))
    | some x₁ =>
      cases d₂ with
      | none =>
        dsimp only at htail₂
        exact absurd htail₂.symm (kemLeaf_ne_concat_raw hleaf₂)
      | some x₂ =>
        dsimp only at htail₁ htail₂
        have hss₁ := (concat_injective htail₁).2
        have hss₂ := (concat_injective htail₂).2
        rw [hss₁, hss₂] at hsh ⊢
        exact aliceBob_kemLeaf_eq i S g hinv henc_inv hs hevA (halice_len32 t hs) hB_ss hsh
  | none =>
    cases d₁ <;> cases d₂ <;> dsimp only at htail₁ htail₂
    · rw [htail₁, htail₂] at hsh ⊢
      exact aliceBob_kemLeaf_eq i S g hinv henc_inv hs hevA (halice_len32 t hs) hB_ss hsh
    · rw [htail₁, htail₂] at hsh
      exact absurd hsh (ShapeModKem.shape_kemLeaf_ne_concat i S g (.inl ⟨_, _, rfl⟩))
    · rw [htail₁, htail₂] at hsh
      exact absurd hsh.symm (ShapeModKem.shape_kemLeaf_ne_concat i S g hleaf₂)
    · rename_i x₁ x₂
      rw [htail₁, htail₂] at hsh ⊢
      obtain ⟨hx_sh, hss_sh⟩ := ShapeModKem.shape_concat_inj i S g hsh
      have hss_eq := aliceBob_kemLeaf_eq i S g hinv henc_inv hs hevA (halice_len32 t hs) hB_ss hss_sh
      obtain ⟨pk₁', t_ek, rfl, hek⟩ := hroles₁.2.2.2 x₁ rfl
      obtain ⟨pk₂', t_opk, rfl, hopk⟩ := hroles₂.2.2.2 x₂ rfl
      have hne_t : t_ek ≠ t_opk := fun h => ekAt_opkAt_false (runTraceMoves r ms) t_ek hek (h ▸ hopk)
      have hx_eq := eq_of_dh_randTerm32_shape_eq_of_ne i S g pk₁' pk₂' t_ek t_opk hne_t hx_sh
      rw [hx_eq, hss_eq]

/-- Opposite-parity terms `u', v'` in `SpineRk (LoggedOrBobIkmRk r ms p x)` with equal shapes are
equal on any reachable trace where `x.ct` is attacker-known and Alice's KEM coins have length 32. -/
theorem oppParity_of_spineRk_bob
    (i : ExternInterpretation) (r : ProtocolSetup) (hne : r.alice ≠ r.bob) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) (p : PreKeyFields) (x : PreKeyRep)
    (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability)
    (hx_ct_ak : x.ct.AttackerKnows (runTraceMoves r ms))
    (halice_len32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r ms) t →
      (gamma i S g (randTerm (t + 1) 32)).length = 32)
    (henc_inv : ∀ pk e, (DY.PQKem.kemEncap pk e).1.AttackerKnows (runTraceMoves r ms) →
      e.AttackerKnows (runTraceMoves r ms) ∨
      ∃ t a b ikA ikB spk pqpk opk ek ct keys,
        (runTraceMoves r ms).EventLoggedAt
          (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) (t + 5) ∧
        pk = pqpk ∧ e = randTerm (t + 1) 32)
    (hbob_ct_ak : ∀ b a ikB ikA spk pqpk opk ek ct keys idx,
      (runTraceMoves r ms).EventLoggedAt
        (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) idx →
      ct.AttackerKnows (runTraceMoves r ms))
    {b' c' : Bool} {u' v' : DY.Bytes}
    (hu' : SpineRk (LoggedOrBobIkmRk r ms p x) b' u')
    (hv' : SpineRk (LoggedOrBobIkmRk r ms p x) c' v')
    (hsh : (gamma' i S g u').shape = (gamma' i S g v').shape)
    (hp : (b' ^^ c') = true) :
    u' = v' :=
  eq_of_shape_eq_of_spineRk i S g
    (ikAt_spkAt_false (runTraceMoves r ms))
    (ekAt_ikAt_false (runTraceMoves r ms))
    (ekAt_spkAt_false (runTraceMoves r ms))
    (ekAt_opkAt_false (runTraceMoves r ms))
    (fun _ _ => loggedOrBobIkmRk_roleHoles hne ms)
    (fun c₁ c₂ _ _ _ _ ss₁ ss₂ _ hB₁ hB₂ hc hss_sh => by
      cases c₁ <;> cases c₂ <;> try cases hc
      · exact loggedOrBobIkmRk_kemSS_eq i r hne S g ms p x hreach hx_ct_ak halice_len32
          henc_inv hbob_ct_ak hB₁ hB₂ hss_sh
      · exact (loggedOrBobIkmRk_kemSS_eq i r hne S g ms p x hreach hx_ct_ak halice_len32
          henc_inv hbob_ct_ak hB₂ hB₁ hss_sh.symm).symm)
    hu' hv' hsh hp

end Symbolic.Swarm.CREF.MacInv
