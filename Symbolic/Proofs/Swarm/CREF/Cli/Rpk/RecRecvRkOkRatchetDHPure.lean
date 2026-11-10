/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.CHistStepPure
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Receiver Ratchet-Key Non-Low-Order Preservation Under DH Ratchet Steps

Proves that a successful `RatchetState.dhRatchetStep` rejects low-order X25519 sender ratchet keys
and therefore preserves `RecRecvRkOk` on the updated session record.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.CHistStep
open Symbolic.Swarm.CREF.TR

cref_open
cref_open_tr

open DY DY.Comparse DY.Libsignal
open DY.Libsignal.TripleRatchet (computeMac)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames
open CryptoGames.LibsignalSession hiding computeMac
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

theorem isLowOrderKey_their_bytes_false_of_dhRatchetStep
    (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh :
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their coins) r0 =
        (.ok ck, r1)) :
    their.bytes.toList.length = 32 ∧
      DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat) = false := by
  refine ⟨their.bytes.2, ?_⟩
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, _hsc, hrc1, _hrc2, _hr1⟩ :=
    Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
  cases hlow : DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat)
  · rfl
  · exfalso
    have hlen_k : their.bytes.toList.length = 32 := their.bytes.2
    have hsec_len :=
      (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList_length
    have hz0 := (hEq.x25519_agreement_zero_iff_low_order
      (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList
      their.bytes.toList hsec_len hlen_k).mpr hlow
    have hlen := hEq.x25519_agreement_length
      (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList their.bytes.toList
    have hz' :
        ((cryptoOf' interpretation E D).X
          (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes) their.bytes).toList =
          List.replicate 32 0#8 := by
      dsimp only [cryptoOf']
      rw [Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hlen]
      exact hz0
    unfold rootCreateChain CryptoGames.Ratchet.createChain at hrc1
    simp only [hz', ite_true] at hrc1
    nomatch hrc1

theorem isLowOrderKey_their_serialize_false_of_dhRatchetStep
    (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh :
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their coins) r0 =
        (.ok ck, r1)) :
    (their.serialize.drop 1).length = 32 ∧
      DY.X25519.isLowOrderKey ((their.serialize.drop 1).map BitVec.toNat) = false := by
  have h := isLowOrderKey_their_bytes_false_of_dhRatchetStep interpretation hEq E D hDh
  simpa [PublicKey.serialize] using h

/-- Preserves `RecRecvRkOk` when every receiver chain key of `rec'` comes from `rec` or equals
`their.serialize` from a successful `RatchetState.dhRatchetStep`. -/
theorem recRecvRkOk_of_subset_or_dhRatchetStep
    (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {rec rec' : RecordRec} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hok : RecRecvRkOk rec)
    (hDh :
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their coins) r0 =
        (.ok ck, r1))
    (hsub : ∀ k ∈ rec'.current.receiverChains.map ChainRec.senderRatchetKey,
      k ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey ∨ k = their.serialize) :
    RecRecvRkOk rec' := by
  intro rc hrc
  rcases hsub rc.senderRatchetKey (List.mem_map_of_mem hrc) with hold | hnew
  · obtain ⟨rc₀, hrc₀, hk⟩ := List.mem_map.mp hold
    rw [← hk]
    exact hok rc₀ hrc₀
  · rw [hnew]
    exact isLowOrderKey_their_serialize_false_of_dhRatchetStep interpretation hEq E D hDh

end Symbolic.Swarm.CREF.CliPure.TR.CHistStep
