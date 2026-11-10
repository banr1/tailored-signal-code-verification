/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.SR.ModelW
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.TRREF.GrowthRecord.DRBound
import Symbolic.Proofs.Swarm.TRREF.GrowthSend
import Symbolic.Proofs.Swarm.CREF.SendWire.Ghosts -- shake: keep

/-!
# Pure Send-Wire Execution, Growth Bounds, and Record Canonicity

Defines `pureEvalSendWire` and `sessionToRecordRecPending`, and proves BitVec key/block round-trip
identities, SPQR send growth bounds, and canonical record-bytes correspondence.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession

cref_open
open DY.Libsignal.Refinement (sha256CompressFunction PbValue encodeField)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record (encSession encSenderChain encReceiverChain encChainKey
  encPendingPreKey encPendingKyber)
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.SR
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure
  (PureBinCanonSession slots_NonEmptyV1Q slots_RecordCanonical_Q TRRecordCanon)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

abbrev SpqrSem := OpaqueSymbolSemantics

theorem extractLsb'_zero_shift8_or_c {n : Nat} (hn : 8 ≤ n) (b : BitVec 8) (acc : BitVec n) :
    ((acc <<< 8) ||| b.zeroExtend n).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hin : i < n := by omega
  simp [hi, hin]

theorem extractLsb'_succ_shift8_or_c {w : Nat} (b : BitVec 8) (acc : BitVec (8 * w))
    (j : Nat) (hj : j + 1 < w) :
    ((acc <<< 8) ||| b.zeroExtend (8 * w)).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 8 * w := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have h4 : 8 * j + i < 8 * w := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [hi, h1, h2, h3, h4, hb]

theorem extractLsb'_bytesToKey32_c (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (CryptoGames.HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [CryptoGames.HKDF.bytesToKey32] using extractLsb'_zero_shift8_or_c (by decide) b _
    | succ j =>
      change (((CryptoGames.HKDF.bytesToKey32 rest : BitVec (8 * 32)) <<< 8) ||| b.zeroExtend (8 * 32)).extractLsb' (8 * (j + 1)) 8 = _
      rw [extractLsb'_succ_shift8_or_c b _ j h32, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem keyToBytes32_bytesToKey32_c (bs : List (BitVec 8)) (h : bs.length = 32) :
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.HMAC.keyToBytes32, h]) fun j _ h2 => ?_
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32_c bs j h2 (by omega)

theorem extractLsb'_bytesToBlock_c (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h16 : j < 16) :
    (CryptoGames.CBC.bytesToBlock bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [CryptoGames.CBC.bytesToBlock] using extractLsb'_zero_shift8_or_c (by decide) b _
    | succ j =>
      change (((CryptoGames.CBC.bytesToBlock rest : BitVec (8 * 16)) <<< 8) ||| b.zeroExtend (8 * 16)).extractLsb' (8 * (j + 1)) 8 = _
      rw [extractLsb'_succ_shift8_or_c b _ j h16, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

theorem blockToBytesLE_bytesToBlock_c (bs : List (BitVec 8)) (h : bs.length = 16) :
    CryptoGames.CBC.blockToBytesLE (CryptoGames.CBC.bytesToBlock bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.CBC.blockToBytesLE, h]) fun j _ h2 => ?_
  simp only [CryptoGames.CBC.blockToBytesLE, List.getElem_ofFn]
  exact extractLsb'_bytesToBlock_c bs j h2 (by omega)

/-! ## `pureEvalSendWire` and SPQR Growth Bounds -/

theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) : Mut.exec (pure a) s = (.ok a, s) := rfl
theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) : Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl
theorem mut_exec_get {σ : Type} (s : σ) : Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl
theorem mut_exec_set {σ : Type} (s' s : σ) : Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl
theorem mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) : Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl
theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) : Mut.exec (liftE r) s = (r, s) := by cases r <;> rfl
theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s = match Mut.exec m s with | (.ok a, s') => Mut.exec (f a) s' | (.error e, s') => (.error e, s') := by
  unfold Mut.exec; change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]; simp only [StateT.run_bind]; rcases (m.run).run s with ⟨r, s'⟩; cases r <;> rfl

/-- Pure `Spqr` view of `S : SpqrModel` without referencing `SpqrModel.spqr` or `S.draws`. -/
def spqrOfModel (S : SpqrModel) : Spqr HwBytes HwBytes :=
  { init := fun _ _ => [], send := S.send, recv := S.recv, sendPanics := S.sendPanics, recvPanics := S.recvPanics }

/-- Pure machine-free `send_wire` evaluation on `sess : Session HwBytes` with associated-data
`pendingAddrs : Option HwBytes` used when `sess.pendingPreKey = some _`. -/
def pureEvalSendWire (C : Crypto) (W : AesW) (S : SpqrModel)
    (sess : Session HwBytes) (pendingAddrs : Option HwBytes) (ptext coins : HwBytes) :
    Option (HwBytes × HwBytes) :=
  match Mut.exec OutgoingTripleRatchet.fromSessionState sess.state with
  | (.error _, _) => none
  | (.ok otr, taken) =>
    match sess.pendingPreKey with
    | none =>
      match Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext none coins) otr with
      | (.error _, _) => none
      | (.ok signalMessage, otr') =>
        some (CryptoVerification.E2E.Record.encodeRecord
          ⟨some { sess with state := otr'.applyToSessionState taken }⟩,
          wireWhisperTag :: signalMessage.serialized)
    | some items =>
      match Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext pendingAddrs coins) otr with
      | (.error _, _) => none
      | (.ok signalMessage, otr') =>
        let kyberPayload := sess.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩
        let psm := PreKeySignalMessage.new 4#8 sess.localRegistrationId items.preKeyId
          items.signedPreKeyId kyberPayload items.baseKey otr.localIdentityKey signalMessage
        some (CryptoVerification.E2E.Record.encodeRecord
          ⟨some { sess with state := otr'.applyToSessionState taken }⟩,
          wirePrekeyTag :: psm.serialized)

theorem mut_exec_fromSessionState_v4 {PQ : Type} [Inhabited PQ] (s : SessionState PQ)
    (sc : SenderChain) (remote : IdentityKey)
    (hver : s.sessionVersion = 4#32) (hsc : s.senderChain = some sc)
    (hrem : s.remoteIdentity = some remote) :
    Mut.exec OutgoingTripleRatchet.fromSessionState s =
      (.ok ⟨sc.ratchetKey, sc.chainKey, s.previousCounter, s.pqRatchetState, 4#8,
          s.localIdentity, remote⟩, { s with pqRatchetState := default }) := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
    SessionState.version
  simp only [mut_exec_bind, mut_exec_get, mut_exec_modifyGet, hsc]
  have hver_cond : ¬ (256 ≤ (if (4#32 : BitVec 32) = 0 then 2 else 4#32).toNat) := by decide
  have hver8 : BitVec.ofNat 8 (if (4#32 : BitVec 32) = 0 then 2 else 4#32).toNat = 4#8 := by decide
  simp only [hver, hrem, hver_cond, ↓reduceIte, mut_exec_pure, hver8]

theorem mut_exec_fromSessionState_props {PQ : Type} [Inhabited PQ] (s : SessionState PQ)
    (o : OutgoingTripleRatchet PQ) (taken : SessionState PQ)
    (h : Mut.exec OutgoingTripleRatchet.fromSessionState s = (.ok o, taken)) :
    o.pqrState = s.pqRatchetState ∧ taken.receiverChains = s.receiverChains := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc
  · simp [hs] at h
  · simp only [hs, mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hr : s.remoteIdentity with _ | k
      · simp [hr] at h
      · simp only [hr, mut_exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
        rw [← h.1, ← h.2]
        exact ⟨rfl, rfl⟩

theorem mut_exec_encryptW_ok_inv {C : Crypto} {W : AesW} {S : SpqrModel}
    {ptext : HwBytes} {ad : Option HwBytes} {coins : HwBytes}
    {o o' : OutgoingTripleRatchet HwBytes} {sm : SignalMessage}
    (h : Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext ad coins) o = (.ok sm, o')) :
    ¬ S.sendPanics o.pqrState coins ∧
    ∃ salt msgPq, S.send o.pqrState coins = some (o'.pqrState, salt, msgPq) := by
  unfold OutgoingTripleRatchet.encryptW at h
  by_cases hpan : S.sendPanics o.pqrState coins = true
  · simp [spqrOfModel, hpan] at h
  · simp only [mut_exec_bind, mut_exec_get, spqrOfModel, hpan, Bool.false_eq_true, ↓reduceIte] at h
    rcases hsend : S.send o.pqrState coins with _ | ⟨pq', salt, msgPq⟩
    · simp [hsend] at h
    · simp only [hsend] at h
      rcases hnck : o.senderChainKey.nextChainKey C.F with e | ck'
      · simp [hnck] at h
      · simp only [hnck, mut_exec_bind, mut_exec_liftE, mut_exec_set, mut_exec_pure,
          Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨_, rfl⟩
        exact ⟨hpan, salt, msgPq, rfl⟩

/-- Inversion of a returning `pureEvalSendWire` call: extracts non-panicking `S.send`, preserved
`receiverChains`, and the updated `encodeRecord` bytes. -/
theorem pureEvalSendWire_some_inv {C : Crypto} {W : AesW} {S : SpqrModel}
    {sess : Session HwBytes} {pendingAddrs : Option HwBytes} {ptext coins : HwBytes}
    {retState retMessage : HwBytes}
    (hev : pureEvalSendWire C W S sess pendingAddrs ptext coins = some (retState, retMessage)) :
    ¬ S.sendPanics sess.state.pqRatchetState coins ∧
    ∃ (st' : SessionState HwBytes) (salt : Salt) (msgPq : HwBytes),
      S.send sess.state.pqRatchetState coins = some (st'.pqRatchetState, salt, msgPq) ∧
      st'.receiverChains = sess.state.receiverChains ∧
      retState = CryptoVerification.E2E.Record.encodeRecord ⟨some { sess with state := st' }⟩ := by
  unfold pureEvalSendWire at hev
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState sess.state with ⟨e | otr, taken⟩
  · simp [hfrom] at hev
  · obtain ⟨hpqr, hrc_taken⟩ := mut_exec_fromSessionState_props sess.state otr taken hfrom
    simp only [hfrom] at hev
    cases hppk : sess.pendingPreKey with
    | none =>
      simp only [hppk] at hev
      rcases henc : Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext none coins) otr with ⟨e | sm, otr'⟩
      · simp [henc] at hev
      · simp only [henc, Option.some.injEq, Prod.mk.injEq] at hev
        obtain ⟨hnp, salt, msgPq, hsend⟩ := mut_exec_encryptW_ok_inv henc
        exact ⟨hpqr ▸ hnp, otr'.applyToSessionState taken, salt, msgPq,
          hpqr ▸ hsend, hrc_taken, hev.1.symm⟩
    | some items =>
      simp only [hppk] at hev
      rcases henc : Mut.exec (OutgoingTripleRatchet.encryptW C W protoSignalCodec (spqrOfModel S) ptext pendingAddrs coins) otr with ⟨e | sm, otr'⟩
      · simp [henc] at hev
      · simp only [henc, Option.some.injEq, Prod.mk.injEq] at hev
        obtain ⟨hnp, salt, msgPq, hsend⟩ := mut_exec_encryptW_ok_inv henc
        exact ⟨hpqr ▸ hnp, otr'.applyToSessionState taken, salt, msgPq,
          hpqr ▸ hsend, hrc_taken, hev.1.symm⟩

theorem pureEvalSendWire_some_send_isSome (C : Crypto) (W : AesW) (S : SpqrModel)
    (sess : Session HwBytes) (pendingAddrs : Option HwBytes) (ptext coins : HwBytes)
    (out : HwBytes × HwBytes)
    (hev : pureEvalSendWire C W S sess pendingAddrs ptext coins = some out) :
    (S.send sess.state.pqRatchetState coins).isSome := by
  obtain ⟨_, st', salt, msgPq, hsend, _, _⟩ := pureEvalSendWire_some_inv hev
  rw [hsend]; rfl

/-- One `send` step at `spqrModelOf i` keeps `SpqrOooBounded` and grows the pq state by `≤ 2^17`. -/
theorem spqrModelOf_send_growth_pure (i : ExternInterpretation) (pq rest pq' : List (BitVec 8))
    (salt : Salt) (msgPq : List (BitVec 8))
    (hb : SpqrOooBounded pq) (hlen : pq.length < 2 ^ 32)
    (h : (spqrModelOf i).send pq rest = some (pq', salt, msgPq)) :
    SpqrOooBounded pq' ∧ pq'.length ≤ pq.length + 2 ^ 17 := by
  have h' : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1WithMac
      (DY.Libsignal.Refinement.sha256CompressFunction i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i)).send pq rest = some (pq', salt, msgPq) := h
  obtain ⟨k, hB⟩ : ∃ k, Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendB
      (DY.Libsignal.Refinement.sha256CompressFunction i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
      (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i) pq rest = some (pq', k, msgPq) := by
    cases salt with
    | none => exact ⟨[], by simp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendB, h']⟩
    | some v => exact ⟨v.toList, by simp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrSendB, h']⟩
  have hg := Symbolic.Swarm.TRREF.spqr_send_growth _ _ _ pq rest pq' k msgPq hb hlen hB
  have h14 : (2 : Nat) ^ 14 ≤ 2 ^ 17 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact ⟨hg.1, le_trans hg.2 (Nat.add_le_add_left h14 _)⟩

/-- Post-encrypt `SpqrOooBounded` preservation and `< 2^32` record-length bound over `PureBinCanonSession`. -/
theorem encodeRecord_lt_32_of_send_growth (i : ExternInterpretation)
    (sess : Session HwBytes) (st' : SessionState HwBytes)
    (coins : HwBytes) (salt : Salt) (msgPq : HwBytes)
    (hcaps : PureBinCanonSession sess)
    (hooo : SpqrOooBounded sess.state.pqRatchetState)
    (hrec : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 32 - 2 ^ 20)
    (hrc_eq : st'.receiverChains = sess.state.receiverChains)
    (hsend : (spqrModelOf i).send sess.state.pqRatchetState coins =
      some (st'.pqRatchetState, salt, msgPq)) :
    SpqrOooBounded st'.pqRatchetState ∧
    (CryptoVerification.E2E.Record.encodeRecord ⟨some { sess with state := st' }⟩).length < 2 ^ 32 := by
  have hpq_le := Symbolic.Swarm.TRREF.GrowthRecord.extLen_add_pq_le_encodeRecord sess
  have hpq_lt : sess.state.pqRatchetState.length < 2 ^ 32 := by omega
  obtain ⟨hooo', hgrow⟩ := spqrModelOf_send_growth_pure i _ coins _ salt msgPq hooo hpq_lt hsend
  refine ⟨hooo', Symbolic.Swarm.TRREF.GrowthRecord.encodeRecord_lt_of_growth sess
    { sess with state := st' } ⟨?_, ?_⟩
    (Symbolic.Swarm.TRREF.GrowthRecord.extLen_applyState_eq sess st').le hgrow hrec⟩
  · simpa [hrc_eq] using hcaps.2.1
  · simpa [hrc_eq] using hcaps.2.2.1

export Symbolic.Swarm.CREF.SendWire
  (encWire encMac encMsg encSt isFreshSendWire updateFreshAt clearSendAddr sendGhost
   isFreshSendWire_encWire sendGhost_addr_encWire gamma_sendGhost_pt gamma_sendGhost_coins)

/-! ## Record Byte Canonicity and `sessionToRecordRecPending` -/

open Swarm.Phase0WholeFunctionBridge

def sessionToRecordRecPending (s : Session (List (BitVec 8))) : RecordRec :=
  { current :=
      { (Swarm.Phase0WholeFunctionBridge.sessionToSessionRec s) with
        pendingPreKey := s.pendingPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingPreKey p, []),
        pendingKyberPreKey := s.pendingKyberPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingKyber p, []) },
    previous := [] }

theorem stateRel_normPending_iff (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) (rec : RecordRec) :
    StateRel interpretation S g st (normPending rec) ↔ StateRel interpretation S g st rec := Iff.rfl

theorem stateRel_sessionToRecordRecPending_iff (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) (s : Session (List (BitVec 8))) :
    StateRel interpretation S g st (sessionToRecordRecPending s) ↔
      StateRel interpretation S g st (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec s) := Iff.rfl

def pbFields_c (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap (fun p => encodeField p.1 0 0 p.2)

theorem pbFields_append_c (l₁ l₂ : List (Nat × PbValue)) :
    pbFields_c (l₁ ++ l₂) = pbFields_c l₁ ++ pbFields_c l₂ := by
  simp only [pbFields_c, List.flatMap_append]

def bytesFieldList_c (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

def u32FieldList_c (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

theorem pbFields_bytesFieldList_c (tag : Nat) (b : HwBytes) :
    pbFields_c (bytesFieldList_c tag b) = bytesField tag b := by
  unfold bytesFieldList_c bytesField; split <;> simp [pbFields_c]

theorem pbFields_u32FieldList_c (tag : Nat) (v : BitVec 32) :
    pbFields_c (u32FieldList_c tag v) = u32Field tag v := by
  unfold u32FieldList_c u32Field; split <;> simp [pbFields_c]

theorem pbFields_map_msgField7_c (l : List ChainRec) :
    pbFields_c (l.map fun c => (7, PbValue.bytes (chainBytes c))) =
    l.flatMap (msgField 7 ∘ chainBytes) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, pbFields_c, List.flatMap_cons, msgField, Function.comp_apply]
    congr 1

def encSessionFields_c (s : Session (List (BitVec 8))) : List (Nat × PbValue) :=
  let st := s.state
  u32FieldList_c 1 st.sessionVersion ++
  bytesFieldList_c 2 st.localIdentity.serialize ++
  bytesFieldList_c 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesFieldList_c 4 (HMAC.keyToBytes32 st.rootKey) ++
  u32FieldList_c 5 st.previousCounter ++
  ((st.senderChain.map (fun c => [(6, PbValue.bytes (chainBytes (Swarm.Phase0WholeFunctionBridge.senderChainToChainRec c)))])).getD []) ++
  (st.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).map (fun c => (7, PbValue.bytes (chainBytes c))) ++
  ((s.pendingPreKey.map (fun p => [(9, PbValue.bytes (encPendingPreKey p))])).getD []) ++
  u32FieldList_c 10 s.remoteRegistrationId ++
  u32FieldList_c 11 s.localRegistrationId ++
  bytesFieldList_c 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map (fun p => [(14, PbValue.bytes (encPendingKyber p))])).getD []) ++
  bytesFieldList_c 15 st.pqRatchetState

theorem encPendingPreKey_length_le_encSession_c (s : Session (List (BitVec 8)))
    (p : PendingPreKey) (hp : s.pendingPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingPreKey p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

theorem encPendingKyber_length_le_encSession_c (s : Session (List (BitVec 8)))
    (p : PendingKyberPreKey) (hp : s.pendingKyberPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingKyber p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

theorem pbFields_singleton_bytes_c (tag : Nat) (b : HwBytes) :
    pbFields_c [(tag, PbValue.bytes b)] = msgField tag b := by
  simp [pbFields_c, msgField]

theorem flatten_map_lenField_length_ge_c (l : List ReceiverChain) (rc : ReceiverChain) (hrc : rc ∈ l) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField 7 (CryptoVerification.E2E.Record.encReceiverChain c)).flatten).length := by
  induction l with
  | nil => cases hrc
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hrc with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

theorem pbFields_encSessionFields_c (s : Session (List (BitVec 8)))
    (halice : s.aliceBaseKey.length < 2 ^ 64) (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    pbFields_c (encSessionFields_c s) = CryptoVerification.E2E.Record.encSession s := by
  have hcb : ∀ c, chainBytes c = DY.Libsignal.TripleRatchet.Refinement.chainBytes c := fun _ => rfl
  have hloc_len : s.state.localIdentity.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
  have hrem_len : ((s.state.remoteIdentity.map IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases s.state.remoteIdentity <;> simp [IdentityKey.serialize, PublicKey.serialize]
  have hrk_len : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by simp [HMAC.keyToBytes32]
  have hsc_eq :
      pbFields_c ((s.state.senderChain.map
        (fun c => [(6, PbValue.bytes (chainBytes (Swarm.Phase0WholeFunctionBridge.senderChainToChainRec c)))])).getD []) =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField,
        Swarm.Phase0WholeFunctionBridge.senderChainToChainRec]
      rw [pbFields_singleton_bytes_c, hcb, Swarm.Phase0WholeFunctionBridge.chainBytes_sender_eq_encSenderChain sc]
      have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
        unfold CryptoVerification.E2E.Record.encSenderChain; dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := Swarm.Phase0WholeFunctionBridge.record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := Swarm.Phase0WholeFunctionBridge.lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey sc.chainKey)
        have h4 := Swarm.Phase0WholeFunctionBridge.encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 6 _ hsc_len
  have hrc_eq :
      pbFields_c ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).map
        (fun c => (7, PbValue.bytes (chainBytes c)))) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
    rw [pbFields_map_msgField7_c, List.flatMap_map, List.flatMap_def]; congr 1
    apply List.map_congr_left; intro rc hrc; dsimp only [Function.comp_apply]
    have hrc_len : (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 := by
      have h1 := flatten_map_lenField_length_ge_c s.state.receiverChains rc hrc
      unfold CryptoVerification.E2E.Record.encSession at hsess_len
      simp only [List.length_append] at hsess_len; omega
    rw [hcb, Swarm.Phase0WholeFunctionBridge.chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc)]
    exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 7 _ hrc_len
  have hppk_eq :
      pbFields_c ((s.pendingPreKey.map
        (fun p => [(9, PbValue.bytes (CryptoVerification.E2E.Record.encPendingPreKey p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_c]
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 9 _
        (lt_of_le_of_lt (encPendingPreKey_length_le_encSession_c s p hppk) hsess_len)
  have hpkp_eq :
      pbFields_c ((s.pendingKyberPreKey.map
        (fun p => [(14, PbValue.bytes (CryptoVerification.E2E.Record.encPendingKyber p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_c]
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 14 _
        (lt_of_le_of_lt (encPendingKyber_length_le_encSession_c s p hpkp) hsess_len)
  unfold encSessionFields_c CryptoVerification.E2E.Record.encSession; dsimp only
  repeat rw [pbFields_append_c]
  rw [hsc_eq, hrc_eq, hppk_eq, hpkp_eq]
  repeat rw [pbFields_u32FieldList_c]
  repeat rw [pbFields_bytesFieldList_c]
  change DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 3 ((Option.map IdentityKey.serialize s.state.remoteIdentity).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
      CryptoVerification.E2E.Record.msgField 6 (Option.map encSenderChain s.state.senderChain) ++
      (List.map (fun c => CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)) s.state.receiverChains).flatten ++
      CryptoVerification.E2E.Record.msgField 9 (Option.map encPendingPreKey s.pendingPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
      CryptoVerification.E2E.Record.msgField 14 (Option.map encPendingKyber s.pendingKyberPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState = _
  rw [Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 1,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 2 _ (by omega),
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 3 _ hrem_len,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 4 _ (by omega),
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 5,
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 10,
      Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 11,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 13 _ halice,
      Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 15 _ hpq]

theorem pbFields_encSessionFields_eq_sessionToRecordRecPending_c (s : Session (List (BitVec 8))) :
    msgField 1 (pbFields_c (encSessionFields_c s)) = recordBytes (sessionToRecordRecPending s) := by
  unfold encSessionFields_c recordBytes sessionToRecordRecPending Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
  dsimp only [List.flatMap_nil, List.append_nil]; repeat rw [pbFields_append_c]
  rw [pbFields_u32FieldList_c, pbFields_bytesFieldList_c, pbFields_bytesFieldList_c,
      pbFields_bytesFieldList_c, pbFields_u32FieldList_c, pbFields_map_msgField7_c,
      pbFields_u32FieldList_c, pbFields_u32FieldList_c, pbFields_bytesFieldList_c, pbFields_bytesFieldList_c]
  cases s.state.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
    simp [Function.comp_def, pbFields_c, msgField]

theorem recordBytes_sessionToRecordRecPending_eq_encodeRecord_64
    (s : Session (List (BitVec 8))) (halice : s.aliceBaseKey.length < 2 ^ 64)
    (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  rw [← pbFields_encSessionFields_eq_sessionToRecordRecPending_c, pbFields_encSessionFields_c s halice hpq hseeds hsess_len]
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
  dsimp only [Option.map_some]; exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 1 _ hsess_len

theorem recordBytes_sessionToRecordRecPending_of_canonical_Q
    {Q : List (BitVec 8) → Prop} {bs : HwBytes} {s : Session (List (BitVec 8))}
    (hc : slots_RecordCanonical_Q Q bs s) :
    recordBytes (sessionToRecordRecPending s) = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  obtain ⟨_, _, ⟨_, _, hchains_sc, halice_lt, _, hpq_lt, hsess_lt⟩⟩ := hc
  have hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk; have h32 := (hchains_sc rc hrc).2 mk hmk; omega
  exact recordBytes_sessionToRecordRecPending_eq_encodeRecord_64 s (by omega) (by omega) hseeds (by omega)

theorem rec_eq_sessionToRecordRec_of_canonical_Q
    {Q : List (BitVec 8) → Prop} {rec : RecordRec} {recBytes : HwBytes} {s : Session (List (BitVec 8))}
    (hrecBytes : recBytes = recordBytes rec) (hc : slots_RecordCanonical_Q Q recBytes s) :
    normPending rec = normPending (sessionToRecordRecPending s) ∧ s.aliceBaseKey.length < 2 ^ 63 ∧
    (∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63) := by
  have hb := recordBytes_sessionToRecordRecPending_of_canonical_Q hc
  obtain ⟨hc1, _, ⟨_, _, hchains_sc, halice_lt, _, _, _⟩⟩ := hc
  refine ⟨Symbolic.Swarm.CREF.TR.recordBytes_injective (by rw [← hrecBytes, hc1, hb]), by omega, fun rc hrc mk hmk => ?_⟩
  have h32 := (hchains_sc rc hrc).2 mk hmk; omega

theorem pendingPreKey_eq_none_of_canon {r₀ : ProtocolSetup} {p : Participant}
    {recBytes : HwBytes} {s : Session (List (BitVec 8))}
    (hcanon : TRRecordCanon r₀ p recBytes) (hrc : slots_RecordCanonical_Q slots_NonEmptyV1Q recBytes s) :
    s.pendingPreKey = none := by
  obtain ⟨sess₀, hc₀, _, _, _, _, hppk₀, _, _⟩ := hcanon
  have hnorm : normPending (sessionToRecordRecPending s) = normPending (sessionToRecordRecPending sess₀) := by
    apply Symbolic.Swarm.CREF.TR.recordBytes_injective
    rw [recordBytes_sessionToRecordRecPending_of_canonical_Q hrc,
        recordBytes_sessionToRecordRecPending_of_canonical_Q hc₀, ← hrc.1, ← hc₀.1]
  have hp := congrArg (fun r => r.current.pendingPreKey) hnorm
  dsimp only [normPending, normPendingS, sessionToRecordRecPending] at hp; rw [hppk₀] at hp
  rcases hppk : s.pendingPreKey with _ | ppk
  · rfl
  · rw [hppk] at hp; cases hp

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set mut_exec_modifyGet mut_exec_liftE mut_exec_bind

end Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure
