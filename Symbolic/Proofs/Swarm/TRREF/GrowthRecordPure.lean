/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecord.DRBound
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.SR.RecvSpecWPure
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.RngG.R3Canon
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.SR.MsgX.TopPureX
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.TopPure

/-!
# Pure Record-Length and OOO Bounds After Decrypt

Record-length `< 2^32` and `SpqrOooBounded` preservation lemmas for `messageDecryptSignalW` at
`pureSpqr (spqrModelOf i)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecordPure

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin (storedSession inMemAnswers)
open CryptoVerification.E2E.Record
open Proofs.libsignal.SR (AesW messageDecryptSignalW)
open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.TRREF.GrowthRecord (DRCaps extLen_add_pq_le_encodeRecord extLen_decrypt_le
  encodeRecord_lt_of_growth)

/-- Projection of an `SpqrModel` to `CryptoGames.LibsignalSession.Spqr`. -/
def pureSpqr (M : SpqrModel) : Spqr (List (BitVec 8)) (List (BitVec 8)) :=
  ⟨fun _ _ => [], M.send, M.recv, M.sendPanics, M.recvPanics⟩

theorem drCaps_of_pureBinCanonSession {s : Session (List (BitVec 8))}
    (h : Symbolic.Swarm.CREF.TR.Pure.PureBinCanonSession s) : DRCaps s := by
  rcases h with ⟨_, hrc_len, hrc_mk, _, _, _, _⟩
  exact ⟨hrc_len, hrc_mk⟩

theorem pq_length_le_encodeRecord_pure (s : Session (List (BitVec 8))) :
    s.state.pqRatchetState.length ≤ (encodeRecord ⟨some s⟩).length := by
  have := extLen_add_pq_le_encodeRecord s
  omega

theorem pq_length_lt_of_hrec_pure (sess : Session (List (BitVec 8)))
    (hrec : (encodeRecord ⟨some sess⟩).length < 2 ^ 32 - 2 ^ 20) :
    sess.state.pqRatchetState.length < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (pq_length_le_encodeRecord_pure sess)
    (Nat.lt_of_lt_of_le hrec (Nat.sub_le _ _))

/-- One successful `recv` step at `spqrModelOf i` preserves `SpqrOooBounded` and grows the PQ
state by at most `2^17` bytes. -/
theorem spqrModelOf_recv_growth_pure (i : ExternInterpretation) (pq m pq' : List (BitVec 8))
    (salt : CryptoGames.HKDF.Salt)
    (hb : SpqrOooBounded pq) (hlen : pq.length < 2 ^ 32)
    (h : (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i)).recv pq m = .ok (pq', salt)) :
    SpqrOooBounded pq' ∧ pq'.length ≤ pq.length + 2 ^ 17 := by
  change (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i).recv pq m = .ok (pq', salt) at h
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1WithMac
    CryptoVerification.LibsignalSpqrV1.toSpqrModel at h
  dsimp only at h
  cases hr : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i))
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith
        (DY.Libsignal.Refinement.sha256CompressFunction i))
      pq m with
  | error e =>
    rw [hr] at h
    rcases e with e | e <;> cases h
  | ok r =>
    rw [hr] at h
    dsimp only at h
    have hst : r.state = pq' := by
      revert h
      cases CryptoVerification.LibsignalSpqrV1.recvKeyToSalt? r.key with
      | none => intro h; cases h
      | some s => intro h; cases h; rfl
    subst hst
    have hB : Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i) pq m = some (r.state, r.key) := by
      simp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB,
        Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1RecvWithMac,
        CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel, hr]
    exact Symbolic.Swarm.TRREF.GrowthRecvPure.spqr_recv_growth _ _ _ pq m r.state r.key hb hlen hB

/-- Polymorphic post-state characterization of `storedSession` after `messageDecryptSignalW`. -/
theorem storedSession_decryptW_post_pure {Addr Key : Type} (C : Crypto) (W : AesW)
    (spqr : Spqr (List (BitVec 8)) Key) (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (rem loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8))) :
    storedSession sess (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg rem loc coins).2
      = sess ∨
      ∃ (st' : SessionState (List (BitVec 8))) (salt : CryptoGames.HKDF.Salt),
        storedSession sess
            (messageDecryptSignalW C W spqr ser (inMemAnswers sess) msg rem loc coins).2 =
          { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } ∧
        spqr.recv sess.state.pqRatchetState msg.pqRatchet = .ok (st'.pqRatchetState, salt) ∧
        ((∀ c ∈ sess.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys) →
          ∀ c ∈ st'.receiverChains, c.messageKeys.length ≤ maxMessageKeys) ∧
        (SeedsLen32 sess.state → SeedsLen32 st') ∧
        (sess.state.receiverChains.length ≤ maxReceiverChains →
          st'.receiverChains.length ≤ maxReceiverChains) := by
  rcases Proofs.libsignal.SR.MsgX.TopPure.storedSession_decryptW_cases C W spqr ser
      msg rem loc coins sess with h | ⟨pt, st', htr, h⟩
  · exact Or.inl h
  · right
    obtain ⟨_, _, _, newPq, salt, -, -, hspqr, -, hst', -⟩ :=
      Proofs.libsignal.RngG.R3.decryptW_ok_branch htr
    obtain ⟨-, -, -, hSeeds, -, hLe, -, -⟩ :=
      Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_state_props htr
    refine ⟨st', salt, h, ?_,
      fun hMk => Proofs.libsignal.SR.MsgX.TopPure.msgKeysLe_of_tryDecryptFromRecordW hMk htr,
      hSeeds, hLe⟩
    rw [hst']
    exact hspqr

/-- Address-polymorphic record-length `< 2^32` bound after `messageDecryptSignalW` at
`pureSpqr (spqrModelOf i)`. -/
theorem encodeRecord_storedSession_decryptW_lt_pure {Addr : Type} (C : Crypto) (W : AesW)
    (i : ExternInterpretation) (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (rem loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8)))
    (hcaps : DRCaps sess) (hooo : SpqrOooBounded sess.state.pqRatchetState)
    (hrec : (encodeRecord ⟨some sess⟩).length < 2 ^ 32 - 2 ^ 20) :
    (encodeRecord ⟨some (storedSession sess
      (messageDecryptSignalW C W (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i)) ser
        (inMemAnswers sess) msg rem loc coins).2)⟩).length < 2 ^ 32 := by
  rcases storedSession_decryptW_post_pure C W
      (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i)) ser msg rem loc coins sess with
    h | ⟨st', salt, h, hrecv, hMk, hSeeds, hLe⟩
  · rw [h]
    exact Nat.lt_of_lt_of_le hrec (Nat.sub_le _ _)
  · rw [h]
    have hgrow := (spqrModelOf_recv_growth_pure i _ _ _ salt hooo
      (pq_length_lt_of_hrec_pure sess hrec) hrecv).2
    refine encodeRecord_lt_of_growth sess
      { sess with state := st', pendingPreKey := none, pendingKyberPreKey := none } ?_
      (extLen_decrypt_le sess st') hgrow hrec
    obtain ⟨hn, hk⟩ := hcaps
    have hMk' := hMk (fun c hc => (hk c hc).1)
    have hSeeds' := hSeeds (fun c hc mk hmk => (hk c hc).2 mk hmk)
    exact ⟨hLe hn, fun c hc => ⟨hMk' c hc, hSeeds' c hc⟩⟩

/-- Address-polymorphic `SpqrOooBounded` preservation after `messageDecryptSignalW` at
`pureSpqr (spqrModelOf i)`. -/
theorem spqrOooBounded_storedSession_decryptW_pure {Addr : Type} (C : Crypto) (W : AesW)
    (i : ExternInterpretation) (ser : Addr → Addr → Option (List (BitVec 8)))
    (msg : SignalMessage) (rem loc : Addr) (coins : BitVec 256)
    (sess : Session (List (BitVec 8)))
    (hooo : SpqrOooBounded sess.state.pqRatchetState)
    (hlen : sess.state.pqRatchetState.length < 2 ^ 32) :
    SpqrOooBounded (storedSession sess
      (messageDecryptSignalW C W (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i)) ser
        (inMemAnswers sess) msg rem loc coins).2).state.pqRatchetState := by
  rcases storedSession_decryptW_post_pure C W
      (pureSpqr (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i)) ser msg rem loc coins sess with
    h | ⟨st', salt, h, hrecv, -, -, -⟩
  · rw [h]; exact hooo
  · rw [h]; exact (spqrModelOf_recv_growth_pure i _ _ _ salt hooo hlen hrecv).1

abbrev spqrOooBounded_recvWire_storedSession := @spqrOooBounded_storedSession_decryptW_pure

end Symbolic.Swarm.TRREF.GrowthRecordPure
