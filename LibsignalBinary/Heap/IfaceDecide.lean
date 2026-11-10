/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Iface
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements

/-!
# Layout Decidability and `RustCliAlloc.atState` Simp Bridges

* `Decidable` instances for `LayoutOk`, `RustLayoutOk`, and `NullAllowed` via the computable
  power-of-two characterization `0 < align ∧ 2 ^ align.log2 = align`.
* `@[simp]` lemmas normalizing `P (A.atState s)` to `P A.repAlloc` across live-only representation
  predicates in `LibsignalBinary.Specifications`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.IfaceDecide

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap
  (RustAlloc LayoutOk vecBuf vecAt vecOf vecU8At vecU8)
open CryptoVerification.LibsignalSessionRepr
  (ChainGhost VecGhost RatchetGhost vecGhostAt messageKeyAt optChainKeyAt chainAt ratchetAt
   consumeMessageKeyResultAt)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost boxU8At optBoxU8At invalidMessageStrAt speAt vecResultAt errResultAt
   signalMessageAt signalMessageResultAt protocolAddressAt optSenderChainAt optTailVecAt sessionStateAt
   otrAt otrResultAt)
open CryptoVerification.LibsignalTripleRatchet
  (VecArg decodeErrorAtStackLen decodeErrorAt spqrSendKeyAt spqrRecvKeyAt spqrRecvResultAt spqrSendResultAt optAddrAt
   recordResultAt)
open CryptoVerification.LibsignalPublicApiRepr
  (RecordGhost sessionStateReprAt sessionRecordAt addrCloneAt apiErrAt apiDecResultAt optKyberAt
   preKeyMsgAt apiEncResultAt)
open CryptoVerification.RecordCodecs
  (PreKeyRecord SignedPreKeyRecord)
open CryptoVerification.RecordCodecsBinary
  (preKeyRecordAt preKeyResultAt identityKeyPairResultAt identityKeyResultAt vecOkResultAt
   boxU8Owned signedPreKeyStructAt kyberPreKeyResultAt signedPreKeyResultAt)
open CryptoVerification.LibsignalSpqrV1
  (optKeyBytesAt recvResultExactKeyAt)
open CryptoGames.LibsignalSession
  (ReceiverChain SessionState)
open CryptoGames.LibsignalSessionApi
  (SessionRecord)
open LibsignalBinary.Heap
  (RustLayoutOk NullAllowed RustCliAlloc)

/-! ## `Decidable` Instances for `LayoutOk`, `RustLayoutOk`, and `NullAllowed` -/

/-- A natural number `align` is a power of two iff `0 < align` and `2 ^ align.log2 = align`. -/
theorem exists_eq_two_pow_iff (align : Nat) :
    (∃ k : Nat, align = 2 ^ k) ↔ (0 < align ∧ 2 ^ align.log2 = align) := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Nat.two_pow_pos k, by rw [Nat.log2_two_pow]⟩
  · rintro ⟨_, h⟩
    exact ⟨align.log2, h.symm⟩

theorem layoutOk_iff (size align : Nat) :
    LayoutOk size align ↔
      0 < size ∧ (0 < align ∧ 2 ^ align.log2 = align) ∧ size + align ≤ 2 ^ 63 := by
  unfold LayoutOk
  rw [exists_eq_two_pow_iff]

theorem rustLayoutOk_iff (size align : Nat) :
    RustLayoutOk size align ↔
      (0 < size ∧ (0 < align ∧ 2 ^ align.log2 = align) ∧ size + align ≤ 2 ^ 63) ∧
        align ≤ 2 ^ 31 := by
  unfold RustLayoutOk
  rw [layoutOk_iff]

theorem nullAllowed_iff (size align : Nat) :
    NullAllowed size align ↔ 2 ^ 62 < size + align :=
  Iff.rfl

instance instDecidableLayoutOk (size align : Nat) : Decidable (LayoutOk size align) :=
  decidable_of_iff _ (layoutOk_iff size align).symm

instance instDecidableRustLayoutOk (size align : Nat) : Decidable (RustLayoutOk size align) :=
  decidable_of_iff _ (rustLayoutOk_iff size align).symm

instance instDecidableNullAllowed (size align : Nat) : Decidable (NullAllowed size align) :=
  inferInstanceAs (Decidable (2 ^ 62 < size + align))

/-! ## `@[simp]` Bridges for `RustCliAlloc.repAlloc` and `RustCliAlloc.atState` -/

@[simp]
theorem _root_.LibsignalBinary.Heap.RustCliAlloc.repAlloc_pool (A : RustCliAlloc) :
    A.repAlloc.pool = emp :=
  rfl

/-! ### `RustHeap.Vec` -/

@[simp]
theorem vecBuf_atState {α : Type} (A : RustCliAlloc) (s : State) :
    @vecBuf α (A.atState s) = @vecBuf α A.repAlloc :=
  rfl

@[simp]
theorem vecAt_atState {α : Type} (A : RustCliAlloc) (s : State) :
    @vecAt α (A.atState s) = @vecAt α A.repAlloc :=
  rfl

@[simp]
theorem vecOf_atState {α : Type} (A : RustCliAlloc) (s : State) :
    @vecOf α (A.atState s) = @vecOf α A.repAlloc :=
  rfl

@[simp]
theorem vecU8At_atState (A : RustCliAlloc) (s : State) :
    vecU8At (A.atState s) = vecU8At A.repAlloc :=
  rfl

@[simp]
theorem vecU8_atState (A : RustCliAlloc) (s : State) :
    vecU8 (A.atState s) = vecU8 A.repAlloc :=
  rfl

/-! ### `LibsignalSessionRepr` -/

@[simp]
theorem vecGhostAt_atState (A : RustCliAlloc) (s : State) :
    vecGhostAt (A.atState s) = vecGhostAt A.repAlloc :=
  rfl

@[simp]
theorem messageKeyAt_atState (A : RustCliAlloc) (s : State) :
    messageKeyAt (A.atState s) = messageKeyAt A.repAlloc :=
  rfl

@[simp]
theorem optChainKeyAt_atState (A : RustCliAlloc) (s : State) :
    optChainKeyAt (A.atState s) = optChainKeyAt A.repAlloc :=
  rfl

@[simp]
theorem chainAt_atState (A : RustCliAlloc) (s : State) :
    chainAt (A.atState s) = chainAt A.repAlloc :=
  rfl

@[simp]
theorem ratchetAt_atState (A : RustCliAlloc) (s : State) :
    ratchetAt (A.atState s) = ratchetAt A.repAlloc :=
  rfl

@[simp]
theorem resultAt_atState (A : RustCliAlloc) (s : State) :
    consumeMessageKeyResultAt (A.atState s) = consumeMessageKeyResultAt A.repAlloc :=
  rfl

/-! ### `LibsignalTripleRatchetRepr` -/

@[simp]
theorem boxU8At_atState (A : RustCliAlloc) (s : State) :
    boxU8At (A.atState s) = boxU8At A.repAlloc :=
  rfl

@[simp]
theorem optBoxU8At_atState (A : RustCliAlloc) (s : State) :
    optBoxU8At (A.atState s) = optBoxU8At A.repAlloc :=
  rfl

@[simp]
theorem invalidMessageStrAt_atState (A : RustCliAlloc) (s : State) :
    invalidMessageStrAt (A.atState s) = invalidMessageStrAt A.repAlloc :=
  rfl

@[simp]
theorem speAt_atState (A : RustCliAlloc) (s : State) :
    speAt (A.atState s) = speAt A.repAlloc :=
  rfl

@[simp]
theorem decResultAt_atState (A : RustCliAlloc) (s : State) :
    vecResultAt (A.atState s) = vecResultAt A.repAlloc :=
  rfl

@[simp]
theorem errResultAt_atState (A : RustCliAlloc) (s : State) :
    errResultAt (A.atState s) = errResultAt A.repAlloc :=
  rfl

@[simp]
theorem signalMessageAt_atState (A : RustCliAlloc) (s : State) :
    signalMessageAt (A.atState s) = signalMessageAt A.repAlloc :=
  rfl

@[simp]
theorem msgResultAt_atState (A : RustCliAlloc) (s : State) :
    signalMessageResultAt (A.atState s) = signalMessageResultAt A.repAlloc :=
  rfl

@[simp]
theorem protocolAddressAt_atState (A : RustCliAlloc) (s : State) :
    protocolAddressAt (A.atState s) = protocolAddressAt A.repAlloc :=
  rfl

@[simp]
theorem optSenderChainAt_atState (A : RustCliAlloc) (s : State) :
    optSenderChainAt (A.atState s) = optSenderChainAt A.repAlloc :=
  rfl

@[simp]
theorem optTailVecAt_atState (A : RustCliAlloc) (s : State) :
    optTailVecAt (A.atState s) = optTailVecAt A.repAlloc :=
  rfl

@[simp]
theorem sessionStateAt_atState (A : RustCliAlloc) (s : State) :
    sessionStateAt (A.atState s) = sessionStateAt A.repAlloc :=
  rfl

@[simp]
theorem otrAt_atState (A : RustCliAlloc) (s : State) :
    otrAt (A.atState s) = otrAt A.repAlloc :=
  rfl

@[simp]
theorem otrResultAt_atState (A : RustCliAlloc) (s : State) :
    otrResultAt (A.atState s) = otrResultAt A.repAlloc :=
  rfl

/-! ### `LibsignalTripleRatchetProst` and `LibsignalTripleRatchet` -/

@[simp]
theorem decodeErrorWith_atState (A : RustCliAlloc) (s : State) :
    decodeErrorAtStackLen (A.atState s) = decodeErrorAtStackLen A.repAlloc :=
  rfl

@[simp]
theorem decodeErrorAt_atState (A : RustCliAlloc) (s : State) :
    decodeErrorAt (A.atState s) = decodeErrorAt A.repAlloc :=
  rfl

@[simp]
theorem optKeyAt_atState (A : RustCliAlloc) (s : State) :
    spqrSendKeyAt (A.atState s) = spqrSendKeyAt A.repAlloc :=
  rfl

@[simp]
theorem optKeyRecvAt_atState (A : RustCliAlloc) (s : State) :
    spqrRecvKeyAt (A.atState s) = spqrRecvKeyAt A.repAlloc :=
  rfl

@[simp]
theorem vecArgAt_atState (A : RustCliAlloc) (s : State) :
    VecArg.at (A.atState s) = VecArg.at A.repAlloc :=
  rfl

@[simp]
theorem recvResultAt_atState (A : RustCliAlloc) (s : State) :
    spqrRecvResultAt (A.atState s) = spqrRecvResultAt A.repAlloc :=
  rfl

@[simp]
theorem sendResultAt_atState (A : RustCliAlloc) (s : State) :
    spqrSendResultAt (A.atState s) = spqrSendResultAt A.repAlloc :=
  rfl

@[simp]
theorem optAddrAt_atState (A : RustCliAlloc) (s : State) :
    optAddrAt (A.atState s) = optAddrAt A.repAlloc :=
  rfl

@[simp]
theorem recordResultAt_atState (A : RustCliAlloc) (s : State) :
    recordResultAt (A.atState s) = recordResultAt A.repAlloc :=
  rfl

/-! ### `LibsignalPublicApiRepr` -/

@[simp]
theorem sessionAt_atState (A : RustCliAlloc) (s : State) :
    sessionStateReprAt (A.atState s) = sessionStateReprAt A.repAlloc :=
  rfl

@[simp]
theorem sessionRecordAt_atState (A : RustCliAlloc) (s : State) :
    sessionRecordAt (A.atState s) = sessionRecordAt A.repAlloc :=
  rfl

@[simp]
theorem addrCloneAt_atState (A : RustCliAlloc) (s : State) :
    addrCloneAt (A.atState s) = addrCloneAt A.repAlloc :=
  rfl

@[simp]
theorem apiErrAt_atState (A : RustCliAlloc) (s : State) :
    apiErrAt (A.atState s) = apiErrAt A.repAlloc :=
  rfl

@[simp]
theorem apiDecResultAt_atState (A : RustCliAlloc) (s : State) :
    apiDecResultAt (A.atState s) = apiDecResultAt A.repAlloc :=
  rfl

@[simp]
theorem optKyberAt_atState (A : RustCliAlloc) (s : State) :
    optKyberAt (A.atState s) = optKyberAt A.repAlloc :=
  rfl

@[simp]
theorem preKeyMsgAt_atState (A : RustCliAlloc) (s : State) :
    preKeyMsgAt (A.atState s) = preKeyMsgAt A.repAlloc :=
  rfl

@[simp]
theorem apiEncResultAt_atState (A : RustCliAlloc) (s : State) :
    apiEncResultAt (A.atState s) = apiEncResultAt A.repAlloc :=
  rfl

/-! ### `RecordCodecsBinary` and `LibsignalSpqrV1` -/

@[simp]
theorem preKeyRecordAt_atState (A : RustCliAlloc) (s : State) :
    preKeyRecordAt (A.atState s) = preKeyRecordAt A.repAlloc :=
  rfl

@[simp]
theorem preKeyResultAt_atState (A : RustCliAlloc) (s : State) :
    preKeyResultAt (A.atState s) = preKeyResultAt A.repAlloc :=
  rfl

@[simp]
theorem identityKeyPairResultAt_atState (A : RustCliAlloc) (s : State) :
    identityKeyPairResultAt (A.atState s) = identityKeyPairResultAt A.repAlloc :=
  rfl

@[simp]
theorem identityKeyResultAt_atState (A : RustCliAlloc) (s : State) :
    identityKeyResultAt (A.atState s) = identityKeyResultAt A.repAlloc :=
  rfl

@[simp]
theorem vecOkResultAt_atState (A : RustCliAlloc) (s : State) :
    vecOkResultAt (A.atState s) = vecOkResultAt A.repAlloc :=
  rfl

@[simp]
theorem boxU8Owned_atState (A : RustCliAlloc) (s : State) :
    boxU8Owned (A.atState s) = boxU8Owned A.repAlloc :=
  rfl

@[simp]
theorem signedPreKeyStructAt_atState (A : RustCliAlloc) (s : State) :
    signedPreKeyStructAt (A.atState s) = signedPreKeyStructAt A.repAlloc :=
  rfl

@[simp]
theorem kyberPreKeyResultAt_atState (A : RustCliAlloc) (s : State) :
    kyberPreKeyResultAt (A.atState s) = kyberPreKeyResultAt A.repAlloc :=
  rfl

@[simp]
theorem signedPreKeyResultAt_atState (A : RustCliAlloc) (s : State) :
    signedPreKeyResultAt (A.atState s) = signedPreKeyResultAt A.repAlloc :=
  rfl

@[simp]
theorem optKeyBytesAt_atState (A : RustCliAlloc) (s : State) :
    optKeyBytesAt (A.atState s) = optKeyBytesAt A.repAlloc :=
  rfl

@[simp]
theorem recvResultAtX_atState (A : RustCliAlloc) (s : State) :
    recvResultExactKeyAt (A.atState s) = recvResultExactKeyAt A.repAlloc :=
  rfl

/-! ## Decidability and Simp Checks -/

section PilotUsageTests

private theorem test_pilot_pqxdh_segBackS7 :
    LayoutOk 23 1 ∧ RustLayoutOk 23 1 ∧ ¬ NullAllowed 23 1 := by
  decide

private theorem test_pilot_ratchet_dhCommitStep12 :
    RustLayoutOk 33 1 ∧ RustLayoutOk 32 1 ∧ ¬ NullAllowed 33 1 ∧ ¬ NullAllowed 32 1 := by
  decide

private theorem test_pilot_prost_decodeErrorFrom :
    RustLayoutOk 72 8 ∧ ¬ NullAllowed 72 8 := by
  decide

private theorem test_pilot_buckets_polys_and_chainClone :
    RustLayoutOk (4 * 104) 8 ∧ RustLayoutOk 70 2 ∧ RustLayoutOk 872 8 ∧
      ¬ NullAllowed (4 * 104) 8 ∧ ¬ NullAllowed 70 2 ∧ ¬ NullAllowed 872 8 := by
  decide

private theorem test_layout_and_nullAllowed_boundaries :
    ¬ LayoutOk 0 1 ∧ ¬ RustLayoutOk 0 8 ∧
      ¬ RustLayoutOk 24 0 ∧ ¬ RustLayoutOk 24 3 ∧ ¬ RustLayoutOk 64 6 ∧
      RustLayoutOk 64 (2 ^ 31) ∧ LayoutOk 64 (2 ^ 32) ∧ ¬ RustLayoutOk 64 (2 ^ 32) ∧
      RustLayoutOk (2 ^ 63 - 8) 8 ∧ ¬ RustLayoutOk (2 ^ 63 - 7) 8 ∧
      ¬ NullAllowed (2 ^ 62 - 8) 8 ∧ NullAllowed (2 ^ 62 - 7) 8 := by
  decide

private theorem test_pilot_dhCommitMain_atState_simp
    (A : RustCliAlloc) (s : State)
    (ss v cap ptr pqPtr ctPtr serPtr addrPtr remA : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (xs : List (ChainGhost × ReceiverChain))
    (pq bs ct : List (BitVec 8)) (ad : Option (List (BitVec 8)))
    (rem : AddrGhost) :
    (sessionStateAt (A.atState s) ss G st ∗
      vecAt (A.atState s) 104 8 (chainAt (A.atState s)) v cap ptr xs ∗
      vecU8At (A.atState s) v cap pqPtr pq ∗
      boxU8At (A.atState s) (v + 24#64) ctPtr ct ∗
      boxU8At (A.atState s) (v + 40#64) serPtr bs ∗
      optBoxU8At (A.atState s) (v + 88#64) addrPtr ad ∗
      protocolAddressAt (A.atState s) rem remA ∗
      (A.atState s).pool ∗
      A.repAlloc.pool) =
    (sessionStateAt A.repAlloc ss G st ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) v cap ptr xs ∗
      vecU8At A.repAlloc v cap pqPtr pq ∗
      boxU8At A.repAlloc (v + 24#64) ctPtr ct ∗
      boxU8At A.repAlloc (v + 40#64) serPtr bs ∗
      optBoxU8At A.repAlloc (v + 88#64) addrPtr ad ∗
      protocolAddressAt A.repAlloc rem remA ∗
      A.pool s) := by
  simp

private theorem test_multi_layer_atState_simp
    (A : RustCliAlloc) (s : State)
    (e r pkA spkR : BitVec 64) (va : VecArg)
    (rg : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
    (pk : PreKeyRecord)
    (spkRes : Except CryptoGames.LibsignalSession.SignalProtocolError SignedPreKeyRecord)
    (rv : Except Bool (List (BitVec 8) × CryptoGames.HKDF.Salt))
    (rvx : Except Bool (List (BitVec 8) × Option (List (BitVec 8)))) :
    (decodeErrorAt (A.atState s) e ∗
      sessionRecordAt (A.atState s) r rg rec ∗
      preKeyRecordAt (A.atState s) pkA pk ∗
      signedPreKeyResultAt (A.atState s) spkR spkRes ∗
      va.at (A.atState s) ∗
      spqrRecvResultAt (A.atState s) r rv ∗
      recvResultExactKeyAt (A.atState s) r rvx) =
    (decodeErrorAt A.repAlloc e ∗
      sessionRecordAt A.repAlloc r rg rec ∗
      preKeyRecordAt A.repAlloc pkA pk ∗
      signedPreKeyResultAt A.repAlloc spkR spkRes ∗
      va.at A.repAlloc ∗
      spqrRecvResultAt A.repAlloc r rv ∗
      recvResultExactKeyAt A.repAlloc r rvx) := by
  simp

private theorem test_decide_kernel_and_simp_decide
    (A : RustCliAlloc) (s : State) (p : BitVec 64) (n al : Nat)
    (h : RustLayoutOk n al) :
    (RustLayoutOk 23 1 ∧ ¬ NullAllowed 23 1) ∧
      ((RustLayoutOk 23 1 ∧ ¬ NullAllowed 23 1 ∧ RustLayoutOk n al) ↔ RustLayoutOk n al) ∧
      ((A.atState s).live p n al = A.repAlloc.live p n al) := by
  refine ⟨by decide +kernel, ?_, by simp⟩
  let _ := h
  simp +decide

end PilotUsageTests

end LibsignalBinary.Heap.IfaceDecide
