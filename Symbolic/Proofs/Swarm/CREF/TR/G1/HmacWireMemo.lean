/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import ProofLib.Lemmas
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.G1Rep
import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
import Symbolic.Proofs.Swarm.CREF.TR.G1.ShapeAddr
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac

/-!
# HMAC-Wire KDF Inversion with Memo Export

Proves `hmac_wire_attackerKnows_inv_memo`: when a received MAC `msg₀.mac = Trunc.trunc8 inp₀` has
attacker-known `inp₀` matching the receiver's `hmac` shape under `(salt₁, seed₁)`, three-stage KDF
inversion yields attacker-known `salt₀` and `seed₀` matching the shapes of `salt₁` and `seed₁`
whose `kdfExtract salt₀ seed₀` and `seed₀` memos lie in `(gamma' t₀).memo`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg trMsgKeys)
open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (hmac lit litByte)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR.G1.Spine (memo_mem_of_concat_right memo_mem_of_kdfExtract_left
  memo_mem_of_kdfExtract_right)

theorem memo_mem_of_trunc8 (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes)
    {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g x).memo) :
    e ∈ (gamma' i S g (Trunc.trunc8 x)).memo := by
  unfold gamma' at he ⊢
  rw [show Trunc.trunc8 x = ({ input := x } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq concretizeTrunc (concretizeAll i S g)]
  simp [concretizeTrunc, node, he]

theorem memo_mem_of_parse_mac (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) {t inp : DY.Bytes}
    {msg : TRSignalMsg} (hparse : parseTrSignalMsg t = some msg) (hmac : msg.mac = Trunc.trunc8 inp)
    {e : DY.Bytes × DY.Bytes × HwBytes} (he : e ∈ (gamma' i S g inp).memo) :
    e ∈ (gamma' i S g t).memo := by
  rw [parseTrSignalMsg_eq_concat hparse, hmac]
  exact memo_mem_of_concat_right i S g _ _ (memo_mem_of_trunc8 i S g _ he)

/-- An attacker-known `inp₀` under the received MAC (`msg₀.mac = trunc8 inp₀`) shape-matching the
receiver's `hmac` under `(salt₁, seed₁)` yields attacker-known `salt₀`, `seed₀` with the shapes of
`salt₁`, `seed₁` whose `kdfExtract salt₀ seed₀` and `seed₀` memos lie in `(gamma' t₀).memo`. -/
theorem hmac_wire_attackerKnows_inv_memo
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (st₁ : TRState) (salt₁ seed₁ peerIk myIk inp₀ : DY.Bytes)
    (hseed₁ : recvSeed st₁ msg₀ = some seed₁)
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
  obtain ⟨salt₀, seed₀, hsalt₀_sh, hseed₀_sh, hprk₀_eq⟩ :=
    kdfExtract_shape_eq_inv_c interpretation S g hprk₀_sh
  have hprk₀_kdf_ak : (KdfExtract.kdfExtract salt₀ seed₀).AttackerKnows T := hprk₀_eq ▸ hprk₀_ak
  obtain ⟨ck₁, hseed₁_eq⟩ := recvSeed_eq_some_kdfExtract hseed₁
  have hseed₀_sh_kdf : (gamma' interpretation S g seed₀).shape =
      KdfExtract.kdfExtract (gamma' interpretation S g ck₁).shape
        (gamma' interpretation S g (litByte 0x01)).shape := by
    rw [hseed₀_sh, hseed₁_eq, shape_kdfExtract_tr]
  have hsalt_seed_ak : salt₀.AttackerKnows T ∧ seed₀.AttackerKnows T := by
    rcases macKdfSafe_c_kdfExtract_inv r₀ ms salt₀ seed₀ hreach hprk₀_kdf_ak with
      hboth | h01 | h02 | hwr1 | ⟨b1, hwr2⟩
    · exact hboth
    · rw [h01] at hseed₀_sh_kdf; unfold litByte at hseed₀_sh_kdf
      rw [shape_literalToBytes] at hseed₀_sh_kdf
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh_kdf)
    · rw [h02] at hseed₀_sh_kdf; unfold litByte at hseed₀_sh_kdf
      rw [shape_literalToBytes] at hseed₀_sh_kdf
      exact False.elim (literal_ne_kdfExtract _ _ _ hseed₀_sh_kdf)
    · rw [hwr1, shape_concat_tr] at hseed₀_sh_kdf
      exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh_kdf)
    · rcases hwr2 with hwr2 | hwr2 | hwr2 <;> {
        rw [hwr2, shape_concat_tr] at hseed₀_sh_kdf
        exact False.elim (concat_ne_kdfExtract _ _ _ _ hseed₀_sh_kdf)
      }
  have hmemo_prk : ∀ e ∈ (gamma' interpretation S g (KdfExtract.kdfExtract salt₀ seed₀)).memo,
      e ∈ (gamma' interpretation S g t₀).memo := by
    intro e he
    rw [← hprk₀_eq] at he
    apply hmemo_inp
    rw [hinp_eq, hs₀_eq]
    exact memo_mem_of_kdfExtract_left interpretation S g _ _
      (memo_mem_of_kdfExtract_left interpretation S g _ _ he)
  exact ⟨salt₀, seed₀, hsalt_seed_ak.1, hsalt_seed_ak.2, hsalt₀_sh, hseed₀_sh, hmemo_prk,
    fun e he => hmemo_prk e (memo_mem_of_kdfExtract_right interpretation S g _ _ he)⟩

end Symbolic.Swarm.CREF.TR.G1
