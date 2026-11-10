/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.CREF.OpkRelC
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Pure Pre-Key Accept Hypotheses

Defines `RecvAcceptContractPure`, `CReadyPure`, and `RpkAcceptHypsPure` over `PureCRel` and
`COpkRelC`, shared across new-session and session-overwrite pre-key proofs.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.Composed.Refinement (opkRemovedIdx)
open DY.Libsignal.PQXDH.Refinement (X25519TorsionFree)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)

/-- Contract facts of an accepting `session_recv_prekey` call on wire `b` returning `sm`, with
parsed wire `p`, 32-byte random draw `d`, Kyber ciphertext `ct_wire`, and plaintext `pt`. -/
structure RecvAcceptContractPure (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (used : Bool) (b : HwBytes) (sm : StateAndMessage)
    (p : PreKeyFields) (d ct_wire pt : HwBytes) : Prop where
  parse : parsePreKeyWire b = some p
  outer_ver : p.version = 4
  spkId_eq : p.signedPreKeyId = r.spkId
  kpkId_eq : p.kyberPreKeyId = some r.kpkId
  kyber_ct : p.kyberCiphertext = some (kyberKey ct_wire)
  ct_len : ct_wire.length = 1568
  d_len : d.length = 32
  opk_ok : p.preKeyId = none ∨ (r.withOpk = true ∧ used = false ∧ p.preKeyId = some r.opkId)
  opk_removed : p.preKeyId.isSome = true →
    (used || (sm.message[opkRemovedIdx]?).any (· != 0#8)) = true
  counter_le : p.inner.counter.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps
  pqRatchet_ne_nil : p.inner.pqRatchet ≠ []
  version : p.inner.messageVersion = BitVec.ofNat 8 DY.Libsignal.PQXDH.messageVersion.toNat
  baseKey_ok : ((p.baseKey.take 33).drop 1).length = 32 ∧
    DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
    DY.X25519.isLowOrderKey (((p.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
    X25519TorsionFree interpretation ((p.baseKey.take 33).drop 1)
  ratchetKey_ok :
    DY.X25519.isLowOrderKey (p.inner.senderRatchetKey.bytes.toList.map BitVec.toNat) = false
  mac_eq : ∀ S : OpaqueSymbolSemantics,
    S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interpretation →
    TR.bobExpectedMacBytes interpretation r S p ct_wire = p.message.drop (p.message.length - 8)
  dec_eq : ∀ S : OpaqueSymbolSemantics,
    S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interpretation →
    interpretation aesCbcDecryptSymbol
      [p.inner.ciphertext,
       TR.trCipherKeyBytes (sha256CompressFunction interpretation)
         (TR.bobSaltSeedBytes interpretation r S p ct_wire).1
         (TR.bobSaltSeedBytes interpretation r S p ct_wire).2,
       (TR.trIvBytes (sha256CompressFunction interpretation)
         (TR.bobSaltSeedBytes interpretation r S p ct_wire).1
         (TR.bobSaltSeedBytes interpretation r S p ct_wire).2).take 16] = some pt

/-- Bundled pre-state invariants `(Clean, PureCRel, COpkRelC)` before a pre-key receive step. -/
def CReadyPure (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes)
    (opkUsed : Bool) (acc : List MachineEvent) : Prop :=
  (∃ g ms, Clean interpretation r S who ok g ms acc) ∧
  PureCRel interpretation r S who ok records sent accepted acc ∧
  COpkRelC interpretation r S who ok opkUsed acc

/-- Pre-state and contract hypotheses for an accepting `session_recv_prekey` call. -/
structure RpkAcceptHypsPure (interpretation : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc : List MachineEvent) (b : HwBytes) (sm : StateAndMessage) (pf : PreKeyFields)
    (d ct_wire pt : HwBytes) : Prop where
  ready : CReadyPure interpretation r S who ok records sent accepted opkUsed acc
  who_cs : who[(callStarts acc).length]? = some r.bob
  hon : HonestIdentity interpretation r b
  pqh : ∀ q, parsePreKeyWire b = some q → PqFromHonest sent q.message
  fresh : ∀ q, parsePreKeyWire b = some q → q.baseKey.take 33 ∉ accepted
  state_lt : sm.state.length < 2 ^ 64
  contract : RecvAcceptContractPure interpretation r opkUsed b sm pf d ct_wire pt

theorem rpk_accept_sendsFit (b d pt : HwBytes) :
    TR.SendsFit [.recv b, .rng d, .accept pt] := by
  intro m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h <;> cases h

theorem rpk_pureCPrevRel_append {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {p : Participant} {rr₀ : RecordRec} {ps : List HwBytes}
    (hc : PureCRecRel interpretation r S g ms p (recordBytes rr₀))
    (h0 : rr₀.previous = []) (hne : ps ≠ []) :
    PureCPrevRel interpretation r S g ms p (recordBytes { rr₀ with previous := ps }) := by
  refine ⟨{ rr₀ with previous := ps }, rfl, hne, ?_⟩
  have hnil : ({ { rr₀ with previous := ps } with previous := [] } : RecordRec) = rr₀ := by
    cases rr₀; subst h0; rfl
  rw [hnil]
  exact hc

theorem rpk_pureCRecRelH_mono {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₁ g₂ : Ghost} {ms₁ ms₂ : List Move} {p : Participant} {b : HwBytes}
    (hf : ∀ x, PureCRecRel interpretation r S g₁ ms₁ p x → PureCRecRel interpretation r S g₂ ms₂ p x)
    (h : PureCRecRelH interpretation r S g₁ ms₁ p b) :
    PureCRecRelH interpretation r S g₂ ms₂ p b := by
  rcases h with h | ⟨rr, hrb, hne, hcur⟩
  · exact Or.inl (hf b h)
  · exact Or.inr ⟨rr, hrb, hne, hf _ hcur⟩

end Symbolic.Swarm.CREF.CliPure
