/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.SlotsZ6Pure
public import Symbolic.Proofs.Hooks2.BridgeXPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Receiver-Chain Key Validity and `CHist` Stepping

Defines `CHist`, bundling receiver ratchet-key length, non-low-order, skipped-key byte-freshness,
and `G1.RecvHistInvTR` across available states, together with the record-level key predicate
`RecRecvRkOk`. Proves `CHist` preservation across state-storing and non-storing trace extensions,
as well as `RecRecvRkOk` at `bobStart`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.CHistStep
open Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Libsignal
open DY.Libsignal.TripleRatchet (RecvChain)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

/-- Conjunction of receiver ratchet-key length, non-low-order, skipped-key byte-freshness, and
receiver-history invariants across available states at `(g, ms)`. -/
def CHist (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ms : List Move) : Prop :=
  RecvRkLensAll interpretation S g r₀ ms ∧
  RecvRkNotLowAll interpretation S g r₀ ms ∧
  SkippedInstallByteFresh interpretation S g r₀ ms ∧
  G1.RecvHistInvTR interpretation S g r₀ ms

/-- Every receiver chain in `rec` has a 32-byte, non-low-order sender ratchet key payload. -/
def RecRecvRkOk (rec : RecordRec) : Prop :=
  ∀ rc ∈ rec.current.receiverChains,
    (rc.senderRatchetKey.drop 1).length = 32 ∧
    DY.X25519.isLowOrderKey ((rc.senderRatchetKey.drop 1).map BitVec.toNat) = false

theorem recvRk_lens_notLow_of_stateRel {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec) (hok : RecRecvRkOk rec) :
    ∀ c ∈ st.recv,
      (gamma interpretation S g c.ratchetKey).length = 32 ∧
      DY.X25519.isLowOrderKey ((gamma interpretation S g c.ratchetKey).map BitVec.toNat) =
        false := by
  intro c hc
  have hmap := RecvHistStep.map_senderRatchetKey_of_stateRel hrel
  have hmem : serializedKey (gamma interpretation S g c.ratchetKey) ∈
      rec.current.receiverChains.map ChainRec.senderRatchetKey := by
    rw [hmap, List.map_map]
    exact List.mem_map_of_mem (f := serializedKey ∘ fun c : RecvChain =>
      gamma interpretation S g c.ratchetKey) hc
  obtain ⟨rc, hrc, hrk⟩ := List.mem_map.mp hmem
  have h := hok rc hrc
  rw [hrk] at h
  simpa [serializedKey, ecKey] using h

theorem recRecvRkOk_of_stateRel {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec)
    (hst : ∀ c ∈ st.recv,
      (gamma interpretation S g c.ratchetKey).length = 32 ∧
      DY.X25519.isLowOrderKey ((gamma interpretation S g c.ratchetKey).map BitVec.toNat) =
        false) :
    RecRecvRkOk rec := by
  intro rc hrc
  have hmap := RecvHistStep.map_senderRatchetKey_of_stateRel hrel
  have hmem : rc.senderRatchetKey ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey :=
    List.mem_map_of_mem hrc
  rw [hmap, List.map_map] at hmem
  obtain ⟨c, hc, hrk⟩ := List.mem_map.mp hmem
  rw [← hrk]
  simpa [serializedKey, ecKey, Function.comp_def] using hst c hc

theorem recRecvRkOk_of_subset {rec rec' : RecordRec} (hok : RecRecvRkOk rec)
    (hsub : ∀ k ∈ rec'.current.receiverChains.map ChainRec.senderRatchetKey,
      k ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey) :
    RecRecvRkOk rec' := by
  intro rc hrc
  obtain ⟨rc₀, hrc₀, hk⟩ := List.mem_map.mp (hsub _ (List.mem_map_of_mem hrc))
  rw [← hk]
  exact hok rc₀ hrc₀

theorem recRecvRkOk_of_cHist_frame {interpretation : ExternInterpretation} {r₀ : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {st : TRState} {rec rec' : RecordRec}
    (hch : CHist interpretation r₀ S g ms)
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hrel : StateRel interpretation S g st rec)
    (hsub : ∀ k ∈ rec'.current.receiverChains.map ChainRec.senderRatchetKey,
      k ∈ rec.current.receiverChains.map ChainRec.senderRatchetKey) :
    RecRecvRkOk rec' :=
  recRecvRkOk_of_subset
    (recRecvRkOk_of_stateRel hrel fun c hc => ⟨hch.1 st hst c hc, hch.2.1 st hst c hc⟩) hsub

/-- Extends `CHist` from `ms` to `ms'` when at most one new state `newSt` (related to `rec'`)
becomes available. -/
theorem cHist_step {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms ms' : List Move} {newSt : TRState} {rec' : RecordRec}
    (hch : CHist interpretation r₀ S g ms)
    (havail : ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms'),
      st ∈ availableStates r₀ (runTraceMoves r₀ ms) ∨ st = newSt)
    (hrel' : StateRel interpretation S g newSt rec')
    (hnd' : (rec'.current.receiverChains.map ChainRec.senderRatchetKey).Nodup)
    (hok' : RecRecvRkOk rec')
    (hbf' : SkippedInstallByteFresh interpretation S g r₀ ms →
      SkippedInstallByteFresh interpretation S g r₀ ms') :
    CHist interpretation r₀ S g ms' := by
  obtain ⟨hlens, hlow, hbf, hhist⟩ := hch
  have hnew := recvRk_lens_notLow_of_stateRel hrel' hok'
  refine ⟨?_, ?_, hbf' hbf, RecvHistStep.recvHistInvTR_step_of_rel hhist havail hrel' hnd'⟩
  · intro st hst c hc
    rcases havail st hst with hold | rfl
    · exact hlens st hold c hc
    · exact (hnew c hc).1
  · intro st hst c hc
    rcases havail st hst with hold | rfl
    · exact hlow st hold c hc
    · exact (hnew c hc).2

/-- Transfers `CHist` from `ms` to `ms'` when no new states become available. -/
theorem cHist_of_noStore {interpretation : ExternInterpretation} {r₀ : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms ms' : List Move}
    (hch : CHist interpretation r₀ S g ms)
    (havail : ∀ st ∈ availableStates r₀ (runTraceMoves r₀ ms'),
      st ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (hbf' : SkippedInstallByteFresh interpretation S g r₀ ms →
      SkippedInstallByteFresh interpretation S g r₀ ms') :
    CHist interpretation r₀ S g ms' := by
  obtain ⟨hlens, hlow, hbf, hhist⟩ := hch
  exact ⟨fun st hst => hlens st (havail st hst), fun st hst => hlow st (havail st hst), hbf' hbf,
    fun st hst => hhist st (havail st hst)⟩

end Symbolic.Swarm.CREF.CliPure.TR.CHistStep

/-! ## Session-start `RecRecvRkOk` -/

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.TR.RecRecvRkOkStart
open Symbolic.Swarm.CREF.TR

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.CliPure.TR.CHistStep (RecRecvRkOk recRecvRkOk_of_stateRel)

theorem consumeMessageKey_ratchetKey (c c' : DY.Libsignal.TripleRatchet.RecvChain)
    (counter : UInt32) (seed : DY.Bytes)
    (h : DY.Libsignal.TripleRatchet.consumeMessageKey c counter = some (seed, c')) :
    c'.ratchetKey = c.ratchetKey := by
  unfold DY.Libsignal.TripleRatchet.consumeMessageKey at h
  split_ifs at h; cases h; rfl

theorem mem_setRecvChain_singleton_ratchetKey (c c' d : DY.Libsignal.TripleRatchet.RecvChain)
    (hrk : c'.ratchetKey = c.ratchetKey)
    (hd : d ∈ DY.Libsignal.TripleRatchet.setRecvChain [c] c') :
    d.ratchetKey = c.ratchetKey := by
  unfold DY.Libsignal.TripleRatchet.setRecvChain at hd
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hd
  subst hd
  split_ifs
  · exact hrk
  · rfl

theorem mem_bobStart_recv_ratchetKey
    (c0 c' d : DY.Libsignal.TripleRatchet.RecvChain)
    (counter : UInt32) (seed : DY.Bytes)
    (hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c0 counter = some (seed, c'))
    (hd : d ∈ DY.Libsignal.TripleRatchet.setRecvChain [c0] c') :
    d.ratchetKey = c0.ratchetKey :=
  mem_setRecvChain_singleton_ratchetKey c0 c' d (consumeMessageKey_ratchetKey c0 c' counter seed hcons) hd

theorem notLowOrder_of_rootCreateChain_cryptoOf' (interpretation : ExternInterpretation)
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (rk : CryptoGames.LibsignalSession.RootKey)
    (their : CryptoGames.LibsignalSession.PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey)
    (r : CryptoGames.LibsignalSession.RootKey × CryptoGames.LibsignalSession.ChainKey)
    (hok : CryptoGames.LibsignalSession.rootCreateChain
      (Proofs.libsignal.Hooks2.cryptoOf' interpretation) rk their our = .ok r) :
    their.bytes.toList.length = 32 ∧
    DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat) = false := by
  refine ⟨their.bytes.toList_length, ?_⟩
  cases h : DY.X25519.isLowOrderKey (their.bytes.toList.map BitVec.toNat)
  · rfl
  · exfalso
    have hsec := (CryptoGames.Ratchet.clampScalar our.bytes).toList_length
    have hlen := hEq.x25519_agreement_length (CryptoGames.Ratchet.clampScalar our.bytes).toList their.bytes.toList
    have hz := (hEq.x25519_agreement_zero_iff_low_order
      (CryptoGames.Ratchet.clampScalar our.bytes).toList their.bytes.toList hsec their.bytes.toList_length).mpr h
    have hz' : ((Proofs.libsignal.Hooks2.cryptoOf' interpretation).X
        (CryptoGames.Ratchet.clampScalar our.bytes) their.bytes).toList = List.replicate 32 0#8 := by
      dsimp only [Proofs.libsignal.Hooks2.cryptoOf']
      rw [Proofs.libsignal.Hooks2.vec32_toList_of_length_32' _ hlen]; exact hz
    unfold CryptoGames.LibsignalSession.rootCreateChain CryptoGames.Ratchet.createChain at hok
    simp only [hz', ite_true] at hok; cases hok

/-- Establishes `RecRecvRkOk` for a `bobStart` state whose single receiver chain comes from
`consumeMessageKey` on `c0`. -/
theorem recRecvRkOk_bobStart (interpretation : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) (rec : RecordRec)
    (c0 c' : DY.Libsignal.TripleRatchet.RecvChain)
    (counter : UInt32) (seed : DY.Bytes)
    (hrel : StateRel interpretation S g st rec)
    (hrecv : st.recv = DY.Libsignal.TripleRatchet.setRecvChain [c0] c')
    (hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c0 counter = some (seed, c'))
    (hlen : (gamma interpretation S g c0.ratchetKey).length = 32)
    (hlow : DY.X25519.isLowOrderKey
      ((gamma interpretation S g c0.ratchetKey).map BitVec.toNat) = false) :
    RecRecvRkOk rec := by
  refine recRecvRkOk_of_stateRel hrel (fun c hc => ?_)
  rw [hrecv] at hc
  rw [mem_bobStart_recv_ratchetKey c0 c' c counter seed hcons hc]
  exact ⟨hlen, hlow⟩

end Symbolic.Swarm.CREF.CliPure.TR.RecRecvRkOkStart
