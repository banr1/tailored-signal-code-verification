/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Msg
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.PbState
import LibsignalBinary.Proofs.SpqrV1Sync.InSyncParty
import ProofLib.SepLogic.WP.StateNorm

/-!
# SPQR V1 Top-Level `send` and `recv` on Honest Serialized States

Combines the braid synchronization invariant (`Braid.InSync`, `RunT`) with the symmetric-chain
invariant (`ChainSync.ChainOk`) to characterize a party's serialized `PqRatchetState` bytes
(`PartyTop`) under `(spqrV1 F K).send` and `(spqrV1 F K).recv`:

* `PartyTop` covers the three `PqRatchetState` storage layouts produced along an honest execution
  (initial `VersionNegotiationPB` with `chain = none`, post-send with both `vn?` and `chain`, and
  post-recv with `vn? = none` and `chain = some chE`), with `chE` satisfying `ChainOk` at epoch
  `chainCur st = st.epoch.toNat - 1 + (if keyedB st then 1 else 0)` and empty send histories
  (`SendPrevNil`).
* `top_init`, `top_send`, `top_recv`, and `top_recv_err` prove initialization, send/receive key
  agreement with the ghost key schedule, and out-of-window rejection whenever the serialized state
  fits in `< 2 ^ 64` bytes (`TopSize.partyTop_length_lt`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.TopSync

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoGames.HKDF (Salt)

/-! ## Chain epoch of a braid state -/

/-- Whether a braid state has already emitted the `EpochSecret` of its current braid epoch
(the four CT-side states after `.headerReceived`). -/
def keyedB {F : ShaCompress} : St F → Bool
  | .ct1Sampled _ | .ekReceivedCt1Sampled _ | .ct1Acknowledged _ | .ct2Sampled _ => true
  | _ => false

/-- Chain epoch reached by an honest party in braid state `st`. -/
def chainCur {F : ShaCompress} (st : St F) : ℕ :=
  st.epoch.toNat - 1 + (if keyedB st then 1 else 0)

/-! ## Serialized top-level state -/

/-- `PqRatchetStatePB` record assembled from braid state `st`, `vn?`, and optional `Chain`. -/
def topPb {F : ShaCompress} (st : St F) (vn? : Option VersionNegotiationPB) (ch? : Option Chain) :
    PqRatchetStatePB V1State :=
  { inner := some st.into_pb, versionNegotiation := vn?, chain := ch?.map Chain.intoPb }

def topBytes (F : ShaCompress) (K : MlKem) (st : St F) (vn? : Option VersionNegotiationPB)
    (ch? : Option Chain) : Bytes :=
  (spqrDeps F K).encodeState (topPb st vn? ch?)

/-- Initial `VersionNegotiationPB` stored by `Top.initialState` (`Version.v1`, `dparams`). -/
def vnOf (dir : Direction) (authKey : Bytes) : VersionNegotiationPB :=
  { authKey := authKey, direction := dir.toI32, minVersion := Version.v1.toI32,
    chainParams := some dparams }

/-- Decodes the braid `States` component from serialized `PqRatchetState` bytes. -/
def braidOf (F : ShaCompress) (K : MlKem) (bytes : Bytes) : Option (St F) :=
  match LibsignalSpqrV1.decodeState (spqrDeps F K) bytes with
  | .ok pb =>
    match pb.inner with
    | some v =>
      match States.from_pb spqrPolyApi (spqrAuthApi F) v with
      | .ok st => some st
      | .error _ => none
    | none => none
  | .error _ => none

/-- Initial braid state for direction `dir` (`init_a` for `.a2b`, `init_b` for `.b2a`). -/
def initStates (F : ShaCompress) (authKey : Bytes) : Direction → Except StatesPanic (St F)
  | .a2b => States.init_a spqrPolyApi (spqrAuthApi F) authKey
  | .b2a => States.init_b spqrPolyApi (spqrAuthApi F) authKey

/-- Every link's send-direction `KeyHistory` is empty (`next_key` never records skipped keys). -/
def SendPrevNil (ch : Chain) : Prop :=
  ∀ l ∈ ch.links, l.send.prev.data = []

/-- Witnessed top-level state invariant joining `topBytes`, `ChainOk`, `chainCur`, and
`SendPrevNil`. -/
structure PartyTopW (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain) :
    Prop where
  hbytes : bytes = topBytes F K st vn? ch?
  hvn : vn? = none ∨ vn? = some (vnOf dir authKey)
  hch : ch? = some chE ∨
    (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
      chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE)
  hok : ChainOk F authKey dir secret sendCtr recvSet chE
  hcur : chE.currentEpoch.toNat = chainCur st
  hsendEp : chE.sendEpoch.toNat = sendEp
  /-- The chain's `sendEpoch` is strictly below the current braid epoch. -/
  hsendLe : sendEp + 1 ≤ st.epoch.toNat
  /-- Every link's send key history is empty (used by `TopSize.partyTop_length_lt`). -/
  hsendPrev : SendPrevNil chE

/-- Existentially quantified top-level honest-party state invariant. -/
def PartyTop (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) : Prop :=
  ∃ vn? ch? chE, PartyTopW F K authKey dir secret st sendEp sendCtr recvSet bytes vn? ch? chE

/-! ## State and chain protobuf round-trips -/

theorem decodeState_topBytes (F : ShaCompress) (K : MlKem) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (hsize : (topBytes F K st vn? ch?).length < 2 ^ 64) :
    LibsignalSpqrV1.decodeState (spqrDeps F K) (topBytes F K st vn? ch?) = .ok (topPb st vn? ch?) :=
  Codec.decodeState_spqrDeps_encodeState F K _ hsize

theorem braidOf_topBytes (F : ShaCompress) (K : MlKem) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (hsize : (topBytes F K st vn? ch?).length < 2 ^ 64)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st) :
    braidOf F K (topBytes F K st vn? ch?) = some st := by
  unfold braidOf
  rw [decodeState_topBytes F K st vn? ch? hsize]
  simp only [topPb, hcodec]

theorem partyTop_braidOf (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hsize : bytes.length < 2 ^ 64)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st) :
    braidOf F K bytes = some st := by
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  rw [hw.hbytes] at hsize ⊢
  exact braidOf_topBytes F K st vn? ch? hsize hcodec

private theorem dch_fromI32_toI32 (dir : Direction) :
    Direction.fromI32? dir.toI32 = some dir := by
  cases dir <;> rfl

private theorem dch_ced_fromPb_intoPb (d : ChainEpochDirection)
    (hd : d.next = [] ∨ d.next.length = 32) :
    ChainEpochDirection.fromPb d.intoPb = .ok d := by
  rcases d with ⟨ctr, next, ⟨prev⟩⟩
  unfold ChainEpochDirection.fromPb ChainEpochDirection.intoPb
  rcases hd with rfl | hlen
  · rfl
  · simp [hlen]

private theorem dch_linksFromPb_map (xs : List ChainEpoch)
    (hxs : ∀ l ∈ xs, (l.send.next = [] ∨ l.send.next.length = 32) ∧
      (l.recv.next = [] ∨ l.recv.next.length = 32)) :
    Chain.linksFromPb (xs.map fun link =>
      { send := some link.send.intoPb, recv := some link.recv.intoPb }) = .ok xs := by
  induction xs with
  | nil => rfl
  | cons l rest ih =>
    rcases hxs l (List.mem_cons_self ..) with ⟨hs, hr⟩
    have hrest := ih (fun l' hl' => hxs l' (List.mem_cons_of_mem _ hl'))
    simp only [List.map_cons, Chain.linksFromPb, dch_ced_fromPb_intoPb l.send hs,
      dch_ced_fromPb_intoPb l.recv hr, hrest, bind, Except.bind, pure, Except.pure]

/-- Any `Chain` satisfying `ChainOk` round-trips through `Chain.fromPb ∘ Chain.intoPb`. -/
theorem chain_fromPb_intoPb (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) :
    Chain.fromPb ch.intoPb = .ok ch := by
  have hlinks : Chain.linksFromPb (ch.links.map fun link =>
      { send := some link.send.intoPb, recv := some link.recv.intoPb }) = .ok ch.links := by
    apply dch_linksFromPb_map
    intro l hl
    rcases List.getElem_of_mem hl with ⟨i, hi, rfl⟩
    have hli : ch.links[i]? = some ch.links[i] := List.getElem?_eq_getElem hi
    have hsend_le := h.hsend_le
    have hlen := h.hlen
    let e := (ch.sendEpoch.toNat - 1) + i
    have he_sub : e - (ch.sendEpoch.toNat - 1) = i := by omega
    refine ⟨?_, ?_⟩
    · by_cases hi0 : i = 0 ∧ 1 ≤ ch.sendEpoch.toNat
      · left
        rcases hi0 with ⟨rfl, h1⟩
        exact h.hsendOld ch.links[0] h1 hli
      · right
        rcases h.hsendDir e (by omega) (by omega) with ⟨l', hl', hs⟩
        rw [he_sub, hli, Option.some.injEq] at hl'
        subst hl'
        rw [hs.hnext]
        exact length_nextAt F _ (length_seedAt F authKey secret dir e) (sendCtr e)
    · right
      rcases h.hrecvDir e (by omega) (by omega) with ⟨l', hl', hr⟩
      rw [he_sub, hli, Option.some.injEq] at hl'
      subst hl'
      rw [hr.hnext]
      exact length_nextAt F _ (length_seedAt F authKey secret dir.switch e) ch.links[i].recv.ctr.toNat
  rcases ch with ⟨cdir, cur, sendEp, links, nextRoot, params⟩
  unfold Chain.fromPb Chain.intoPb
  simp only [dch_fromI32_toI32, hlinks, bind, Except.bind, pure, Except.pure]

/-- `chainFromVersionNegotiation` on `vnOf dir authKey` initializes epoch counters to `0`. -/
theorem chainFromVN_fresh (F : ShaCompress) (dir : Direction) (authKey : Bytes) (ch : Chain)
    (h : chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok ch) :
    ch.currentEpoch = 0#64 ∧ ch.sendEpoch = 0#64 := by
  unfold chainFromVersionNegotiation vnOf Chain.new at h
  simp only [dch_fromI32_toI32, bind, Except.bind, Except.ok.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

/-! ## Preservation of `SendPrevNil` -/

theorem chainNew_sendPrevNil (hkdf : HkdfFn) (initialKey : Bytes) (dir : Direction)
    (params : ChainParamsPB) (ch : Chain) (h : Chain.new hkdf initialKey dir params = .ok ch) :
    SendPrevNil ch := by
  simp only [Chain.new, Except.ok.injEq] at h
  subst h
  intro l hl
  simp only [List.mem_singleton] at hl
  subst hl
  rfl

theorem chainFromVN_sendPrevNil (F : ShaCompress) (dir : Direction) (authKey : Bytes) (ch : Chain)
    (h : chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok ch) :
    SendPrevNil ch := by
  unfold chainFromVersionNegotiation vnOf at h
  simp only [dch_fromI32_toI32, bind, Except.bind] at h
  exact chainNew_sendPrevNil _ _ _ _ ch h

theorem addEpoch_sendPrevNil (hkdf : HkdfFn) (ch ch' : Chain) (es : EpochSecret)
    (hs : SendPrevNil ch) (h : ch.addEpoch hkdf es = .ok ch') : SendPrevNil ch' := by
  unfold Chain.addEpoch at h
  split_ifs at h
  simp only [Except.ok.injEq] at h
  subst h
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · exact hs l hl
  · simp only [List.mem_singleton] at hl
    subst hl
    rfl

private theorem dsp_addEpoch_opt (hkdf : HkdfFn) (chE chain1 : Chain) (key : Option EpochSecret)
    (hs : SendPrevNil chE)
    (hadd : (match key with
      | some es => chE.addEpoch hkdf es
      | none => .ok chE) = .ok chain1) : SendPrevNil chain1 := by
  cases key with
  | none => cases hadd; exact hs
  | some es => exact addEpoch_sendPrevNil hkdf chE chain1 es hs hadd

private theorem dsp_clearSendNextPrefix (n : ℕ) (xs : List ChainEpoch)
    (hs : ∀ l ∈ xs, l.send.prev.data = []) :
    ∀ l ∈ Chain.clearSendNextPrefix n xs, l.send.prev.data = [] := by
  induction xs generalizing n with
  | nil => cases n <;> simp [Chain.clearSendNextPrefix]
  | cons x xs ih =>
    cases n with
    | zero => exact hs
    | succ n =>
      intro l hl
      simp only [Chain.clearSendNextPrefix, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hs x (List.mem_cons_self ..)
      · exact ih n (fun l hl => hs l (List.mem_cons_of_mem _ hl)) l hl

private theorem dsp_nextKey_prev0 (hkdf : HkdfFn) (d d' : ChainEpochDirection)
    (out : BitVec 32 × Bytes) (h : d.nextKey hkdf = .ok (d', out)) : d'.prev = d.prev := by
  unfold ChainEpochDirection.nextKey at h
  cases hn : ChainEpochDirection.nextKeyInternal hkdf d.next d.ctr with
  | error p => simp [hn, bind, Except.bind] at h
  | ok r =>
    obtain ⟨next', ctr', k⟩ := r
    simp only [hn, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]

private theorem dsp_nextKey_prev (hkdf : HkdfFn) (d : ChainEpochDirection)
    (v : ChainEpochDirection × BitVec 32 × Bytes)
    (h : ChainResult.ofPanic (d.nextKey hkdf) = .ok v) : v.1.prev = d.prev := by
  cases hnk : d.nextKey hkdf with
  | error p => simp [hnk, ChainResult.ofPanic] at h
  | ok r =>
    simp only [hnk, ChainResult.ofPanic, Except.ok.injEq] at h
    subst h
    exact dsp_nextKey_prev0 hkdf d r.1 r.2 hnk

private theorem dsp_set (xs : List ChainEpoch) (i : ℕ) (l' : ChainEpoch)
    (hs : ∀ l ∈ xs, l.send.prev.data = []) (h' : l'.send.prev.data = []) :
    ∀ l ∈ xs.set i l', l.send.prev.data = [] := by
  intro l hl
  rcases List.mem_or_eq_of_mem_set hl with hl | rfl
  · exact hs l hl
  · exact h'

theorem sendKey_sendPrevNil (hkdf : HkdfFn) (ch ch' : Chain) (e : Epoch)
    (out : BitVec 32 × Bytes) (hs : SendPrevNil ch) (h : ch.sendKey hkdf e = .ok (ch', out)) :
    SendPrevNil ch' := by
  unfold Chain.sendKey at h
  by_cases hlt : e < ch.sendEpoch
  · simp [hlt] at h
  simp only [hlt, ↓reduceIte] at h
  cases hidx : ch.epochIdx e with
  | error err => simp [hidx, ChainResult.ofError, bind, Except.bind] at h
  | ok idx0 =>
    simp only [hidx, ChainResult.ofError, bind, Except.bind] at h
    by_cases hne : (ch.sendEpoch != e) = true
    · simp only [hne, ↓reduceIte] at h
      have hxs := dsp_clearSendNextPrefix (idx0 - (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        (ch.links.drop (idx0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH))
        (fun l hl => hs l (List.mem_of_mem_drop hl))
      split at h
      · cases h
      · rename_i link hlink
        split at h
        · cases h
        · rename_i v hv
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          refine dsp_set _ _ _ hxs ?_
          show v.1.prev.data = []
          rw [dsp_nextKey_prev hkdf link.send v hv]
          exact hxs link (List.mem_iff_getElem?.mpr ⟨_, hlink⟩)
    · simp only [hne] at h
      have hxs : ∀ l ∈ ch.links, l.send.prev.data = [] := hs
      split at h
      · cases h
      · rename_i link hlink
        split at h
        · cases h
        · rename_i v hv
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          refine dsp_set _ _ _ hxs ?_
          show v.1.prev.data = []
          rw [dsp_nextKey_prev hkdf link.send v hv]
          exact hxs link (List.mem_iff_getElem?.mpr ⟨_, hlink⟩)

theorem recvKey_sendPrevNil (hkdf : HkdfFn) (ch ch' : Chain) (e : Epoch) (idx : BitVec 32)
    (out : Bytes) (hs : SendPrevNil ch) (h : ch.recvKey hkdf e idx = .ok (ch', out)) :
    SendPrevNil ch' := by
  unfold Chain.recvKey at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hs
  cases hidx : ch.epochIdx e with
  | error err => simp [hidx, ChainResult.ofError, bind, Except.bind] at h
  | ok i =>
    simp only [hidx, ChainResult.ofError, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i link hlink
      split at h
      · cases h
      · rename_i v hv
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact dsp_set ch.links i _ hs (hs link (List.mem_iff_getElem?.mpr ⟨_, hlink⟩))

theorem serialize_head (m : Msg) (idx : BitVec 32) :
    ∃ rest, Message.serialize m idx = 1#8 :: rest :=
  ⟨_, Codec.serialize_eq m idx⟩

theorem msg_roundtrip (F : ShaCompress) (K : MlKem) (m : Msg) (idx : BitVec 32)
    (he : m.epoch ≠ 0#64) (hp : m.payload ≠ .ct1Ack false) :
    ∃ rem, msgPreamble (Message.serialize m idx) =
        .ok { version := 1#8, epoch := m.epoch, index := idx, remaining := rem } ∧
      (spqrDeps F K).msgDeserialize m.epoch rem = .ok m :=
  Codec.spqrDeps_preamble_msgDeserialize_serialize F K m idx he hp

/-! ## Braid epoch and key-output invariants -/

private theorem dfa_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem dfa_ofPanic_ok {p α : Type} [ToStatesPanic p] {x : Except p α} {a : α}
    (h : StatesResult.ofPanic x = .ok a) : x = .ok a := by
  cases x <;> cases h
  rfl

private theorem dfa_not_gt_toNat {a b : Epoch} (h : ¬ (a > b)) : a.toNat ≤ b.toNat := by
  simp only [gt_iff_lt, BitVec.lt_def] at h
  omega

private theorem dfa_add_one_toNat_of_beq_allOnes_false {e : Epoch}
    (h : (e == BitVec.allOnes 64) = false) :
    (e + 1#64).toNat = e.toNat + 1 := by
  have hne : e.toNat ≠ (BitVec.allOnes 64).toNat := by
    intro heq
    have he : e = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq heq
    subst he
    revert h
    decide
  have hall : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := rfl
  have hlt : e.toNat < 2 ^ 64 := e.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem dfa_keysUnsampled_send_hdr_chunk (K : MlKem) (P : PolyApi) {Au : AuthApi}
    (self : Chunked.SendEk.KeysUnsampled Au) (tape : Bytes)
    (s' : Chunked.SendEk.KeysSampled P Au) (c : P.Chunk) (tape' : Bytes)
    (h : self.send_hdr_chunk K P tape = .ok (s', c, tape')) :
    s'.epoch = self.epoch := by
  unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk at h
  obtain ⟨⟨uc, toSend, mac, tape1⟩, huc, h⟩ := dfa_bind_ok h
  obtain ⟨enc, _, h⟩ := dfa_bind_ok h
  obtain ⟨⟨enc', chunk⟩, _, h⟩ := dfa_bind_ok h
  cases h
  unfold Unchunked.SendEk.KeysUnsampled.send_header at huc
  obtain ⟨⟨keys, tape2⟩, _, huc⟩ := dfa_bind_ok huc
  obtain ⟨mac', _, huc⟩ := dfa_bind_ok huc
  cases huc
  rfl

private theorem dfa_headerReceived_send_ct1_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.HeaderReceived P Au) (tape : Bytes)
    (s' : Chunked.SendCt.Ct1Sampled P Au) (c : P.Chunk) (es : EpochSecret) (tape' : Bytes)
    (h : self.send_ct1_chunk K tape = .ok (s', c, es, tape')) :
    s'.epoch = self.epoch ∧ es.epoch = self.epoch := by
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk at h
  obtain ⟨⟨uc, ct1, es', tape1⟩, huc, h⟩ := dfa_bind_ok h
  obtain ⟨enc, _, h⟩ := dfa_bind_ok h
  obtain ⟨⟨enc', chunk⟩, _, h⟩ := dfa_bind_ok h
  cases h
  unfold Unchunked.SendCt.HeaderReceived.send_ct1 at huc
  obtain ⟨⟨⟨ct1', es0, sec0⟩, tape2⟩, _, huc⟩ := dfa_bind_ok huc
  obtain ⟨sec, _, huc⟩ := dfa_bind_ok huc
  obtain ⟨auth, _, huc⟩ := dfa_bind_ok huc
  cases huc
  exact ⟨rfl, rfl⟩

/-- Epoch and payload invariants of `States.send`: preserves `epoch`, never emits `.ct1Ack false`,
and outputs an `EpochSecret` iff transitioning from unkeyed to keyed (`keyedB`). -/
theorem send_facts (F : ShaCompress) (K : MlKem) (st st' : St F) (tape tape' : Bytes) (m : Msg)
    (key : Option EpochSecret)
    (h : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape')) :
    m.epoch = st.epoch ∧ st'.epoch = st.epoch ∧ m.payload ≠ .ct1Ack false ∧
      ((key = none ∧ keyedB st' = keyedB st) ∨
        (∃ es, key = some es ∧ es.epoch = st.epoch ∧ keyedB st = false ∧ keyedB st' = true)) := by
  cases st with
  | keysUnsampled state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c, t'⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    exact ⟨rfl, dfa_keysUnsampled_send_hdr_chunk K spqrPolyApi state tape s' c t' (dfa_ofPanic_ok h1),
      nofun, Or.inl ⟨rfl, rfl⟩⟩
  | keysSampled state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | headerSent state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendEk.HeaderSent.send_ek_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | ct1Received state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendEk.Ct1Received.send_ek_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | ekSentCt1Received state =>
    dsimp only [States.send] at h
    cases h
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | noHeaderReceived state =>
    dsimp only [States.send] at h
    cases h
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | headerReceived state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c, es, t'⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    obtain ⟨he1, he2⟩ := dfa_headerReceived_send_ct1_chunk K state tape s' c es t' (dfa_ofPanic_ok h1)
    exact ⟨rfl, he1, nofun, Or.inr ⟨es, rfl, he2, rfl, rfl⟩⟩
  | ct1Sampled state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | ekReceivedCt1Sampled state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | ct1Acknowledged state =>
    dsimp only [States.send] at h
    cases h
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩
  | ct2Sampled state =>
    dsimp only [States.send] at h
    obtain ⟨⟨s', c⟩, h1, h⟩ := dfa_bind_ok h
    cases h
    have h1' := dfa_ofPanic_ok h1
    unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at h1'
    obtain ⟨⟨enc, chunk⟩, _, h1'⟩ := dfa_bind_ok h1'
    cases h1'
    exact ⟨rfl, rfl, nofun, Or.inl ⟨rfl, rfl⟩⟩

private theorem dfa_keysSampled_recv_ct1_chunk {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendEk.KeysSampled P Au) (ep : Epoch) (chunk : P.Chunk)
    (s' : Chunked.SendEk.HeaderSent P Au)
    (h : self.recv_ct1_chunk ep chunk = .ok s') :
    s'.epoch = self.epoch := by
  unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h
  split at h
  · cases h
  · obtain ⟨dec, _, h⟩ := dfa_bind_ok h
    obtain ⟨dec', _, h⟩ := dfa_bind_ok h
    obtain ⟨enc, _, h⟩ := dfa_bind_ok h
    cases h
    rfl

private theorem dfa_headerSent_recv_ct1_chunk {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendEk.HeaderSent P Au) (ep : Epoch) (chunk : P.Chunk)
    (res : Chunked.SendEk.HeaderSentRecvChunk P Au)
    (h : self.recv_ct1_chunk ep chunk = .ok res) :
    match res with
    | .stillReceiving s' => s'.epoch = self.epoch
    | .done s' => s'.epoch = self.epoch := by
  unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at h
  split at h
  · cases h
  · obtain ⟨dec, _, h⟩ := dfa_bind_ok h
    obtain ⟨dec?, _, h⟩ := dfa_bind_ok h
    cases dec? with
    | none =>
      cases h
      rfl
    | some decoded =>
      obtain ⟨uc, huc, h⟩ := dfa_bind_ok h
      cases h
      unfold Unchunked.SendEk.EkSent.recv_ct1 at huc
      split at huc
      · cases huc
      · cases huc
        rfl

private theorem dfa_ct1Received_recv_ct2_chunk {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendEk.Ct1Received P Au) (ep : Epoch) (chunk : P.Chunk)
    (s' : Chunked.SendEk.EkSentCt1Received P Au)
    (h : self.recv_ct2_chunk ep chunk = .ok s') :
    s'.epoch = self.epoch := by
  unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at h
  split at h
  · cases h
  · obtain ⟨dec, _, h⟩ := dfa_bind_ok h
    obtain ⟨dec', _, h⟩ := dfa_bind_ok h
    cases h
    rfl

private theorem dfa_unchunked_recv_ct2 (K : MlKem) {Au : AuthApi}
    (self : Unchunked.SendEk.EkSentCt1Received Au) (ct2 : Ciphertext2) (mac : Mac)
    (uc : Unchunked.SendCt.NoHeaderReceived Au) (sec : EpochSecret)
    (h : self.recv_ct2 K ct2 mac = .ok (uc, sec)) :
    sec.epoch = self.epoch ∧ uc.epoch.toNat = self.epoch.toNat + 1 := by
  unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at h
  obtain ⟨ss0, _, h⟩ := dfa_bind_ok h
  obtain ⟨ss, _, h⟩ := dfa_bind_ok h
  obtain ⟨auth, _, h⟩ := dfa_bind_ok h
  obtain ⟨vres, _, h⟩ := dfa_bind_ok h
  cases vres with
  | error _ => cases h
  | ok u =>
    dsimp only at h
    rcases h5 : (self.epoch == BitVec.allOnes 64) with _ | _ <;> rw [h5] at h
    · cases h
      exact ⟨rfl, dfa_add_one_toNat_of_beq_allOnes_false h5⟩
    · cases h

private theorem dfa_ekSentCt1Received_recv_ct2_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendEk.EkSentCt1Received P Au) (ep : Epoch) (chunk : P.Chunk)
    (res : Chunked.SendEk.EkSentCt1ReceivedRecvChunk P Au)
    (h : self.recv_ct2_chunk K ep chunk = .ok res) :
    match res with
    | .stillReceiving s' => s'.epoch = self.epoch
    | .done (s', sec) => sec.epoch = self.epoch ∧ s'.epoch.toNat = self.epoch.toNat + 1 := by
  unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h
  split at h
  · cases h
  · obtain ⟨dec, _, h⟩ := dfa_bind_ok h
    obtain ⟨dec?, _, h⟩ := dfa_bind_ok h
    cases dec? with
    | none =>
      cases h
      rfl
    | some ct2Full =>
      dsimp only at h
      split at h
      · cases h
      · obtain ⟨⟨uc, sec⟩, huc, h⟩ := dfa_bind_ok h
        obtain ⟨rHdr, _, h⟩ := dfa_bind_ok h
        cases h
        exact dfa_unchunked_recv_ct2 K self.uc _ _ uc sec huc

private theorem dfa_noHeaderReceived_recv_hdr_chunk {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.NoHeaderReceived P Au) (ep : Epoch) (chunk : P.Chunk)
    (res : Chunked.SendCt.NoHeaderReceivedRecvChunk P Au)
    (h : self.recv_hdr_chunk ep chunk = .ok res) :
    match res with
    | .stillReceiving s' => s'.epoch = self.epoch
    | .done s' => s'.epoch = self.epoch := by
  unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h
  split at h
  · cases h
  · obtain ⟨dec, _, h⟩ := dfa_bind_ok h
    obtain ⟨dec?, _, h⟩ := dfa_bind_ok h
    cases dec? with
    | none =>
      cases h
      rfl
    | some hdrFull =>
      dsimp only at h
      split at h
      · cases h
      · obtain ⟨rEkRes, _, h⟩ := dfa_bind_ok h
        obtain ⟨uc, huc, h⟩ := dfa_bind_ok h
        cases rEkRes with
        | error _ => cases h
        | ok rEk =>
          cases h
          unfold Unchunked.SendCt.NoHeaderReceived.recv_header at huc
          split at huc
          · cases huc
          · obtain ⟨vres, _, huc⟩ := dfa_bind_ok huc
            cases vres <;> cases huc
            rfl

private theorem dfa_unchunked_recv_ek (K : MlKem) {Au : AuthApi}
    (self : Unchunked.SendCt.Ct1Sent Au) (ep : Epoch) (ek : EncapsulationKey)
    (uc : Unchunked.SendCt.Ct1SentEkReceived Au)
    (h : self.recv_ek K ep ek = .ok uc) :
    uc.epoch = self.epoch := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

private theorem dfa_unchunked_send_ct2 (K : MlKem) {Au : AuthApi}
    (self : Unchunked.SendCt.Ct1SentEkReceived Au)
    (uc : Unchunked.SendCt.Ct2Sent Au) (ct2 : Ciphertext2) (mac : Mac)
    (h : self.send_ct2 K = .ok (uc, ct2, mac)) :
    uc.epoch = self.epoch := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at h
  obtain ⟨ct2', _, h⟩ := dfa_bind_ok h
  obtain ⟨mac', _, h⟩ := dfa_bind_ok h
  cases h
  rfl

private theorem dfa_ct1Sampled_recv_ek_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.Ct1Sampled P Au) (ep : Epoch) (chunk : P.Chunk) (ack : Bool)
    (res : Chunked.SendCt.Ct1SampledRecvChunk P Au)
    (h : self.recv_ek_chunk K ep chunk ack = .ok res) :
    match res with
    | .stillReceivingStillSending s' => s'.epoch = self.epoch
    | .stillReceiving s' => s'.epoch = self.epoch
    | .stillSending s' => s'.epoch = self.epoch
    | .done s' => s'.epoch = self.epoch := by
  unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h
  obtain ⟨dec, _, h⟩ := dfa_bind_ok h
  obtain ⟨dec?, _, h⟩ := dfa_bind_ok h
  cases dec? with
  | none =>
    cases ack <;> cases h <;> rfl
  | some decoded =>
    obtain ⟨uc, huc, h⟩ := dfa_bind_ok h
    have he1 := dfa_unchunked_recv_ek K self.uc ep decoded uc huc
    cases ack with
    | false =>
      cases h
      exact he1
    | true =>
      dsimp only [↓reduceIte] at h
      obtain ⟨⟨uc2, ct2, mac⟩, h2, h⟩ := dfa_bind_ok h
      obtain ⟨enc, _, h⟩ := dfa_bind_ok h
      cases h
      exact (dfa_unchunked_send_ct2 K uc uc2 ct2 mac (dfa_ofPanic_ok h2)).trans he1

private theorem dfa_ekReceivedCt1Sampled_recv_ct1_ack (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.EkReceivedCt1Sampled P Au) (ep : Epoch)
    (s' : Chunked.SendCt.Ct2Sampled P Au)
    (h : self.recv_ct1_ack K ep = .ok s') :
    s'.epoch = self.epoch := by
  unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h
  split at h
  · cases h
  · obtain ⟨⟨uc, ct2, mac⟩, h1, h⟩ := dfa_bind_ok h
    obtain ⟨enc, _, h⟩ := dfa_bind_ok h
    cases h
    exact dfa_unchunked_send_ct2 K self.uc uc ct2 mac h1

private theorem dfa_ct1Acknowledged_recv_ek_chunk (K : MlKem) {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.Ct1Acknowledged P Au) (ep : Epoch) (chunk : P.Chunk)
    (res : Chunked.SendCt.Ct1AcknowledgedRecvChunk P Au)
    (h : self.recv_ek_chunk K ep chunk = .ok res) :
    match res with
    | .stillReceiving s' => s'.epoch = self.epoch
    | .done s' => s'.epoch = self.epoch := by
  unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h
  obtain ⟨dec, _, h⟩ := dfa_bind_ok h
  obtain ⟨dec?, _, h⟩ := dfa_bind_ok h
  cases dec? with
  | none =>
    cases h
    rfl
  | some decoded =>
    obtain ⟨uc, huc, h⟩ := dfa_bind_ok h
    obtain ⟨⟨uc2, ct2, mac⟩, h2, h⟩ := dfa_bind_ok h
    obtain ⟨enc, _, h⟩ := dfa_bind_ok h
    cases h
    exact (dfa_unchunked_send_ct2 K uc uc2 ct2 mac (dfa_ofPanic_ok h2)).trans
      (dfa_unchunked_recv_ek K self.uc ep decoded uc huc)

private theorem dfa_ct2Sampled_recv_next_epoch {P : PolyApi} {Au : AuthApi}
    (self : Chunked.SendCt.Ct2Sampled P Au) (ep : Epoch)
    (s' : Chunked.SendEk.KeysUnsampled Au)
    (h : self.recv_next_epoch ep = .ok s') :
    s'.epoch.toNat = self.epoch.toNat + 1 := by
  unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch at h
  obtain ⟨uc, huc, h⟩ := dfa_bind_ok h
  cases h
  unfold Unchunked.SendCt.Ct2Sent.recv_next_epoch at huc
  rcases h1 : (self.uc.epoch == BitVec.allOnes 64) with _ | _ <;> rw [h1] at huc
  · simp only [Bool.false_eq_true, ↓reduceIte] at huc
    split at huc
    · cases huc
    · cases huc
      exact dfa_add_one_toNat_of_beq_allOnes_false h1
  · cases huc

/-- Epoch and key-output invariants of `States.recv`: either keeps `chainCur` without outputting
a key or outputs the current epoch's secret while advancing `epoch` by `1`. -/
theorem recv_facts (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (key : Option EpochSecret) (h : st.recv K m = .ok { key := key, state := st' }) :
    m.epoch.toNat ≤ st'.epoch.toNat ∧
      ((key = none ∧
          ((st'.epoch = st.epoch ∧ keyedB st' = keyedB st) ∨
           (st'.epoch.toNat = st.epoch.toNat + 1 ∧ keyedB st = true ∧ keyedB st' = false))) ∨
        (∃ es, key = some es ∧ es.epoch = st.epoch ∧
          st'.epoch.toNat = st.epoch.toNat + 1 ∧ keyedB st = false ∧ keyedB st' = false)) := by
  cases st with
  | keysUnsampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      cases h
      exact ⟨dfa_not_gt_toNat hgt, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  | keysSampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩)
        rename_i chunk
        obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have he := dfa_keysSampled_recv_ct1_chunk state m.epoch chunk s' (dfa_ofPanic_ok h1)
        exact ⟨by simpa only [States.epoch, he] using hle, Or.inl ⟨rfl, Or.inl ⟨he, rfl⟩⟩⟩
  | headerSent state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_headerSent_recv_ct1_chunk state m.epoch chunk res (dfa_ofPanic_ok h1)
        cases res with
        | stillReceiving s' =>
          cases h
          exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
        | done s' =>
          cases h
          exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
  | ct1Received state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩)
        rename_i chunk
        obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have he := dfa_ct1Received_recv_ct2_chunk state m.epoch chunk s' (dfa_ofPanic_ok h1)
        exact ⟨by simpa only [States.epoch, he] using hle, Or.inl ⟨rfl, Or.inl ⟨he, rfl⟩⟩⟩
  | ekSentCt1Received state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_ekSentCt1Received_recv_ct2_chunk K state m.epoch chunk res h1
        cases res with
        | stillReceiving s' =>
          cases h
          exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
        | done pair =>
          rcases pair with ⟨s', sec⟩
          cases h
          obtain ⟨hsec, hs'⟩ := hres
          have hle' : m.epoch.toNat ≤ (States.noHeaderReceived s').epoch.toNat := by
            change m.epoch.toNat ≤ s'.epoch.toNat
            omega
          exact ⟨hle', Or.inr ⟨sec, rfl, hsec, hs', rfl, rfl⟩⟩
  | noHeaderReceived state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_noHeaderReceived_recv_hdr_chunk state m.epoch chunk res h1
        cases res with
        | stillReceiving s' =>
          cases h
          exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
        | done s' =>
          cases h
          exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
  | headerReceived state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      cases h
      exact ⟨dfa_not_gt_toNat hgt, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  | ct1Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · split at h
        · cases h
          exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
        · rename_i chunk ack _
          obtain ⟨res, h1, h⟩ := dfa_bind_ok h
          have hres := dfa_ct1Sampled_recv_ek_chunk K state m.epoch chunk ack res h1
          cases res with
          | stillReceivingStillSending s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
          | stillReceiving s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
          | stillSending s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
          | done s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
  | ekReceivedCt1Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · split at h <;> simp only [↓reduceIte, Bool.false_eq_true] at h
        · obtain ⟨s', h1, h⟩ := dfa_bind_ok h
          cases h
          have he := dfa_ekReceivedCt1Sampled_recv_ct1_ack K state m.epoch s' (dfa_ofPanic_ok h1)
          exact ⟨by simpa only [States.epoch, he] using hle, Or.inl ⟨rfl, Or.inl ⟨he, rfl⟩⟩⟩
        · obtain ⟨s', h1, h⟩ := dfa_bind_ok h
          cases h
          have he := dfa_ekReceivedCt1Sampled_recv_ct1_ack K state m.epoch s' (dfa_ofPanic_ok h1)
          exact ⟨by simpa only [States.epoch, he] using hle, Or.inl ⟨rfl, Or.inl ⟨he, rfl⟩⟩⟩
        · cases h
          exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
  | ct1Acknowledged state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · rename_i hgt
      have hle := dfa_not_gt_toNat hgt
      split at h
      · cases h; exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
      · split at h
        · cases h
          exact ⟨hle, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
        · rename_i chunk _
          obtain ⟨res, h1, h⟩ := dfa_bind_ok h
          have hres := dfa_ct1Acknowledged_recv_ek_chunk K state m.epoch chunk res h1
          cases res with
          | stillReceiving s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
          | done s' =>
            cases h
            exact ⟨by simpa only [States.epoch, hres] using hle, Or.inl ⟨rfl, Or.inl ⟨hres, rfl⟩⟩⟩
  | ct2Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · rename_i hgt
      split at h
      · rename_i heq
        obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have hs' := dfa_ct2Sampled_recv_next_epoch state m.epoch s' (dfa_ofPanic_ok h1)
        have hm : m.epoch = state.epoch + 1#64 := beq_iff_eq.mp heq
        have hle : m.epoch.toNat ≤ s'.epoch.toNat := by
          rw [hs', hm, BitVec.toNat_add, BitVec.toNat_ofNat]
          exact Nat.mod_le _ _
        exact ⟨hle, Or.inl ⟨rfl, Or.inr ⟨hs', rfl, rfl⟩⟩⟩
      · cases h
    · rename_i hgt
      cases h
      exact ⟨dfa_not_gt_toNat hgt, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩

theorem rec_recv_epoch_causal (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (key : Option EpochSecret) (h : st.recv K m = .ok { key := key, state := st' }) :
    st'.epoch.toNat ≤ max st.epoch.toNat (m.epoch.toNat + 1) := by
  cases st with
  | keysUnsampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · cases h
      exact le_max_left _ _
  | keysSampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact le_max_left _ _)
        rename_i chunk
        obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have he := dfa_keysSampled_recv_ct1_chunk state m.epoch chunk s' (dfa_ofPanic_ok h1)
        simpa only [States.epoch, he] using le_max_left _ _
  | headerSent state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact le_max_left _ _)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_headerSent_recv_ct1_chunk state m.epoch chunk res (dfa_ofPanic_ok h1)
        cases res with
        | stillReceiving s' =>
          cases h
          simpa only [States.epoch, hres] using le_max_left _ _
        | done s' =>
          cases h
          simpa only [States.epoch, hres] using le_max_left _ _
  | ct1Received state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact le_max_left _ _)
        rename_i chunk
        obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have he := dfa_ct1Received_recv_ct2_chunk state m.epoch chunk s' (dfa_ofPanic_ok h1)
        simpa only [States.epoch, he] using le_max_left _ _
  | ekSentCt1Received state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · rename_i hlt
        cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact le_max_left _ _)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_ekSentCt1Received_recv_ct2_chunk K state m.epoch chunk res h1
        cases res with
        | stillReceiving s' =>
          cases h
          simpa only [States.epoch, hres] using le_max_left _ _
        | done pair =>
          rcases pair with ⟨s', sec⟩
          cases h
          obtain ⟨_, hs'⟩ := hres
          simp only [BitVec.lt_def] at hlt
          change s'.epoch.toNat ≤ max state.epoch.toNat (m.epoch.toNat + 1)
          omega
  | noHeaderReceived state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · cases hp : m.payload <;> rw [hp] at h <;> try (cases h; exact le_max_left _ _)
        rename_i chunk
        obtain ⟨res, h1, h⟩ := dfa_bind_ok h
        have hres := dfa_noHeaderReceived_recv_hdr_chunk state m.epoch chunk res h1
        cases res with
        | stillReceiving s' =>
          cases h
          simpa only [States.epoch, hres] using le_max_left _ _
        | done s' =>
          cases h
          simpa only [States.epoch, hres] using le_max_left _ _
  | headerReceived state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · cases h
      exact le_max_left _ _
  | ct1Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · split at h
        · cases h
          exact le_max_left _ _
        · rename_i chunk ack _
          obtain ⟨res, h1, h⟩ := dfa_bind_ok h
          have hres := dfa_ct1Sampled_recv_ek_chunk K state m.epoch chunk ack res h1
          cases res with
          | stillReceivingStillSending s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
          | stillReceiving s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
          | stillSending s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
          | done s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
  | ekReceivedCt1Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · split at h <;> simp only [↓reduceIte, Bool.false_eq_true] at h
        · obtain ⟨s', h1, h⟩ := dfa_bind_ok h
          cases h
          have he := dfa_ekReceivedCt1Sampled_recv_ct1_ack K state m.epoch s' (dfa_ofPanic_ok h1)
          simpa only [States.epoch, he] using le_max_left _ _
        · obtain ⟨s', h1, h⟩ := dfa_bind_ok h
          cases h
          have he := dfa_ekReceivedCt1Sampled_recv_ct1_ack K state m.epoch s' (dfa_ofPanic_ok h1)
          simpa only [States.epoch, he] using le_max_left _ _
        · cases h
          exact le_max_left _ _
  | ct1Acknowledged state =>
    dsimp only [States.recv] at h
    split at h
    · cases h
    · split at h
      · cases h; exact le_max_left _ _
      · split at h
        · cases h
          exact le_max_left _ _
        · rename_i chunk _
          obtain ⟨res, h1, h⟩ := dfa_bind_ok h
          have hres := dfa_ct1Acknowledged_recv_ek_chunk K state m.epoch chunk res h1
          cases res with
          | stillReceiving s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
          | done s' =>
            cases h
            simpa only [States.epoch, hres] using le_max_left _ _
  | ct2Sampled state =>
    dsimp only [States.recv] at h
    split at h
    · rename_i hgt
      split at h
      · obtain ⟨s', h1, h⟩ := dfa_bind_ok h
        cases h
        have hs' := dfa_ct2Sampled_recv_next_epoch state m.epoch s' (dfa_ofPanic_ok h1)
        simp only [gt_iff_lt, BitVec.lt_def] at hgt
        change s'.epoch.toNat ≤ max state.epoch.toNat (m.epoch.toNat + 1)
        omega
      · cases h
    · cases h
      exact le_max_left _ _


theorem chainCur_send_key (F : ShaCompress) (K : MlKem) (st st' : St F) (tape tape' : Bytes)
    (m : Msg) (es : EpochSecret) (hep : 1 ≤ st.epoch.toNat)
    (h : st.send K tape = .ok ({ msg := m, key := some es, state := st' }, tape')) :
    es.epoch.toNat = chainCur st + 1 ∧ chainCur st' = chainCur st + 1 := by
  obtain ⟨-, he', -, hk⟩ := send_facts F K st st' tape tape' m (some es) h
  rcases hk with ⟨h1, -⟩ | ⟨es', h1, h2, h3, h4⟩
  · exact absurd h1 (by simp)
  · cases h1
    have hc : chainCur st = st.epoch.toNat - 1 := by simp [chainCur, h3]
    have hc' : chainCur st' = st.epoch.toNat := by simp [chainCur, h4, he']; omega
    rw [hc, hc', h2]
    omega

theorem chainCur_send_none (F : ShaCompress) (K : MlKem) (st st' : St F) (tape tape' : Bytes)
    (m : Msg) (h : st.send K tape = .ok ({ msg := m, key := none, state := st' }, tape')) :
    chainCur st' = chainCur st := by
  obtain ⟨-, he', -, hk⟩ := send_facts F K st st' tape tape' m none h
  rcases hk with ⟨-, h2⟩ | ⟨es', h1, -⟩
  · unfold chainCur; rw [he', h2]
  · exact absurd h1 (by simp)

theorem chainCur_recv_key (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (es : EpochSecret) (hep : 1 ≤ st.epoch.toNat)
    (h : st.recv K m = .ok { key := some es, state := st' }) :
    es.epoch.toNat = chainCur st + 1 ∧ chainCur st' = chainCur st + 1 := by
  obtain ⟨-, hk⟩ := recv_facts F K st st' m (some es) h
  rcases hk with ⟨h1, -⟩ | ⟨es', h1, h2, h3, h4, h5⟩
  · exact absurd h1 (by simp)
  · cases h1
    have hc : chainCur st = st.epoch.toNat - 1 := by simp [chainCur, h4]
    have hc' : chainCur st' = st.epoch.toNat := by simp [chainCur, h5, h3]
    rw [hc, hc', h2]
    omega

theorem chainCur_recv_none (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (hep : 1 ≤ st.epoch.toNat) (h : st.recv K m = .ok { key := none, state := st' }) :
    chainCur st' = chainCur st := by
  obtain ⟨-, hk⟩ := recv_facts F K st st' m none h
  rcases hk with ⟨-, ⟨h2, h3⟩ | ⟨h2, h3, h4⟩⟩ | ⟨es', h1, -⟩
  · unfold chainCur; rw [h2, h3]
  · have hc : chainCur st = st.epoch.toNat := by simp [chainCur, h3]; omega
    have hc' : chainCur st' = st.epoch.toNat := by simp [chainCur, h4, h2]
    rw [hc, hc']
  · exact absurd h1 (by simp)

theorem epoch_sub_one_le_chainCur {F : ShaCompress} (st : St F) :
    st.epoch.toNat - 1 ≤ chainCur st := by
  unfold chainCur; omega

theorem chainCur_le {F : ShaCompress} (st : St F) (hep : 1 ≤ st.epoch.toNat) :
    chainCur st ≤ st.epoch.toNat := by
  unfold chainCur; split <;> omega

theorem partyTop_epoch_pos {F : ShaCompress} {K : MlKem} {authKey : Bytes} {dir : Direction}
    {secret : ℕ → Bytes} {st : St F} {sendEp : ℕ} {sendCtr : ℕ → ℕ} {recvSet : ℕ → Finset ℕ}
    {bytes : Bytes} (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes) :
    1 ≤ st.epoch.toNat := by
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  have := hw.hsendLe
  omega

theorem partyTop_sendEp_le {F : ShaCompress} {K : MlKem} {authKey : Bytes} {dir : Direction}
    {secret : ℕ → Bytes} {st : St F} {sendEp : ℕ} {sendCtr : ℕ → ℕ} {recvSet : ℕ → Finset ℕ}
    {bytes : Bytes} (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes) :
    sendEp ≤ chainCur st := by
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  have := hw.hok.hsend_le
  rw [hw.hcur, hw.hsendEp] at this
  exact this

/-- `PartyTop` depends on the ghost `secret` schedule only up to `chainCur st`. -/
theorem partyTop_congr {F : ShaCompress} {K : MlKem} {authKey : Bytes} {dir : Direction}
    {secret : ℕ → Bytes} (secret' : ℕ → Bytes) {st : St F} {sendEp : ℕ} {sendCtr : ℕ → ℕ}
    {recvSet : ℕ → Finset ℕ} {bytes : Bytes}
    (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hs : ∀ e, 1 ≤ e → e ≤ chainCur st → secret' e = secret e) :
    PartyTop F K authKey dir secret' st sendEp sendCtr recvSet bytes := by
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  refine ⟨vn?, ch?, chE, hw.hbytes, hw.hvn, hw.hch, ?_, hw.hcur, hw.hsendEp, hw.hsendLe,
    hw.hsendPrev⟩
  exact chainOk_congr F authKey dir secret secret' sendCtr recvSet chE hw.hok
    (fun e h1 h2 => hs e h1 (by rw [← hw.hcur]; exact h2))

/-! ## Chain-epoch bounds on in-flight messages -/

private theorem dix_toXOkE_epoch_le {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator}
    {c : Coins} {m : Msg} (hm : ToXOkE F K e auth c m) : m.epoch.toNat ≤ e.toNat := by
  rcases hm with hlt | rfl | ⟨_, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
  · rw [BitVec.lt_def] at hlt; omega
  · rfl
  · rfl
  · rfl

private theorem dix_xShapeE_epoch_le {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator}
    {c : Coins} {x : St F} (he : e.toNat + 1 < 2 ^ 64) (hx : XShapeE F K e auth c x) :
    e.toNat ≤ x.epoch.toNat := by
  rcases c with _ | s | ⟨s, r⟩
  · rcases hx with rfl; rfl
  · rcases hx with ⟨_, _, rfl⟩; rfl
  · rcases hx with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [States.epoch, Chunked.SendCt.NoHeaderReceived.epoch, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      omega

/-- Every message in `toX` has epoch at most `chainCur x + 1`. -/
theorem inSyncE_toX_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (m : Msg) (hm : m ∈ toX) : m.epoch.toNat ≤ chainCur x + 1 := by
  have hm_le := dix_toXOkE_epoch_le (h.htoX m hm)
  have hx_le := dix_xShapeE_epoch_le h.hepoch h.hx
  have hcur := epoch_sub_one_le_chainCur x
  omega

private theorem diy_yShapeE_epoch {F : ShaCompress} {K : MlKem} {e : Epoch} {auth : Authenticator}
    {c : Coins} {y : St F} (hy : YShapeE F K e auth c y) : y.epoch = e := by
  cases c with
  | init =>
    rcases hy with rfl
    rfl
  | seed s =>
    rcases hy with ⟨_, _, -, -, rfl⟩ | rfl <;> rfl
  | both s r =>
    rcases hy with ⟨_, _, _, -, -, -, rfl⟩ | ⟨_, -, rfl⟩ | ⟨_, _, -, -, rfl⟩ | ⟨_, -, rfl⟩ <;> rfl

/-- Every message in `toY` has epoch at most `chainCur y + 1`. -/
theorem inSyncE_toY_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (m : Msg) (hm : m ∈ toY) : m.epoch.toNat ≤ chainCur y + 1 := by
  have hyep : y.epoch = e := diy_yShapeE_epoch h.hy
  have hcur : e.toNat ≤ chainCur y + 1 := by
    have := epoch_sub_one_le_chainCur y
    rw [hyep] at this
    omega
  rcases h.htoY m hm with hlt | ⟨s, -, idx, rfl⟩ | ⟨s, r, -, hmsg⟩ | rfl
  · rw [BitVec.lt_def] at hlt; omega
  · exact hcur
  · rcases hmsg with ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl <;> exact hcur
  · obtain ⟨s, r, hc, hxlag⟩ := h.hlag hm
    obtain ⟨enc, -, rfl⟩ := h.hcausal s r hc (Or.inr (Or.inl hxlag))
    have he1 : (noneMsg (e + 1#64)).epoch.toNat = e.toNat + 1 := by
      simp only [noneMsg, BitVec.toNat_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt h.hepoch
    rw [he1]
    simp only [chainCur, States.epoch, Chunked.SendCt.Ct2Sampled.epoch, keyedB, ↓reduceIte]
    omega

theorem inSync_toA_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toA) : m.epoch.toNat ≤ chainCur stA + 1 := by
  rcases hs : ekSide e with _ | _
  · exact inSyncE_toX_chainCur F K e auth c stA stB toB toA ((inSync_of_a hs).1 h) m hm
  · exact inSyncE_toY_chainCur F K e auth c stB stA toA toB ((inSync_of_b hs).1 h) m hm

theorem inSync_toB_chainCur (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (m : Msg) (hm : m ∈ toB) : m.epoch.toNat ≤ chainCur stB + 1 := by
  rcases hs : ekSide e with _ | _
  · exact inSyncE_toY_chainCur F K e auth c stA stB toB toA ((inSync_of_a hs).1 h) m hm
  · exact inSyncE_toX_chainCur F K e auth c stB stA toA toB ((inSync_of_b hs).1 h) m hm

/-! ## Unfolding `Top.send` and `Top.recv` on `topBytes` -/

/-- `LibsignalSpqrV1.send` on `topBytes` decodes `st`, runs `st.send`, and delegates to
`sendAfterStates`. -/
theorem send_topBytes (F : ShaCompress) (K : MlKem) (st st' : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (tape tape' : Bytes) (m : Msg)
    (key : Option EpochSecret)
    (hsize : (topBytes F K st vn? ch?).length < 2 ^ 64)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st)
    (h : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape')) :
    LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) (topBytes F K st vn? ch?) tape =
      (sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st', tape') := by
  unfold LibsignalSpqrV1.send
  rw [decodeState_topBytes F K st vn? ch? hsize]
  simp only [topPb, spqrDeps, hcodec, liftStatesResult, h]

/-- The `Ordering.equal` v1 message-handling branch of `Top.recv`. -/
def recvEqual (F : ShaCompress) (K : MlKem) (st : St F) (vn? : Option VersionNegotiationPB)
    (ch? : Option Chain) (pre : MsgPreamble) : SpqrApiResult Recv := do
  let sckaMsg ← (spqrDeps F K).msgDeserialize pre.epoch pre.remaining
  let st0 ← (spqrDeps F K).statesFromPb st.into_pb
  let (key, st1) ← (spqrDeps F K).statesRecv st0 sckaMsg
  if pre.epoch == 0#64 then
    .error (.panic .recvEpochUnderflow)
  else do
    let chain0 ← SpqrApiResult.ofError
      (chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) vn?)
    let chain1 ←
      match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => pure chain0
    let (chain2, msgKey) ←
      SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index)
    let newStateBytes := (spqrDeps F K).encodeState
      { inner := some ((spqrDeps F K).statesIntoPb st1), versionNegotiation := none,
        chain := some chain2.intoPb }
    let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
    .ok { state := newStateBytes, key := outKey }

/-- `LibsignalSpqrV1.recv` on `topBytes` and a version-1 preamble dispatches to `recvEqual`. -/
theorem recv_topBytes (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (msgBytes : Bytes) (pre : MsgPreamble)
    (hsize : (topBytes F K st vn? ch?).length < 2 ^ 64)
    (hvn : vn? = none ∨ vn? = some (vnOf dir authKey))
    (hpre : msgPreamble msgBytes = .ok pre) (hver : pre.version = 1#8) :
    LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) (topBytes F K st vn? ch?) msgBytes =
      recvEqual F K st vn? ch? pre := by
  cases pre with
  | mk ver ep idx rem =>
    subst hver
    rcases hvn with rfl | rfl <;> {
      unfold LibsignalSpqrV1.recv recvEqual
      rw [hpre, decodeState_topBytes F K st _ ch? hsize]
      rfl
    }

/-! ## Party-level `init`, `send`, and `recv` specifications -/

private theorem dti_initStates_facts (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection)
    (k : BitVec 256) (st : St F)
    (hst : initStates F (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir) =
      .ok st) :
    spqrV1Init F K spqrdir k =
      topBytes F K st
        (some (vnOf (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)))
        none ∧
      st.epoch.toNat = 1 ∧ chainCur st = 0 := by
  have hdec : ∀ n, n = 96 → spqrPolyApi.decoder_new n = .ok (.ok (freshDec 96)) := by
    rintro n rfl
    simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
  cases spqrdir with
  | a2b =>
    change States.init_a spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) = .ok st at hst
    have ha : States.init_a spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) =
        .ok (.keysUnsampled
          { uc := { epoch := 1#64, auth := Authenticator.new F (CryptoGames.HMAC.keyToBytes32 k) 1#64 } }) := rfl
    rw [ha] at hst
    cases hst
    exact ⟨rfl, rfl, rfl⟩
  | b2a =>
    change States.init_b spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) = .ok st at hst
    have hb : States.init_b spqrPolyApi (spqrAuthApi F) (CryptoGames.HMAC.keyToBytes32 k) =
        .ok (.noHeaderReceived
          { uc := { epoch := 1#64, auth := Authenticator.new F (CryptoGames.HMAC.keyToBytes32 k) 1#64 },
            receiving_hdr := freshDec 96 }) := by
      simp only [States.init_b, Chunked.SendCt.NoHeaderReceived.new]
      rw [hdec]
      all_goals rfl
    rw [hb] at hst
    cases hst
    refine ⟨?_, rfl, rfl⟩
    simp only [spqrV1Init, spqrV1InitialStateFor, initialState, libsignalSpqrParams,
      libsignalChainParams_false, Direction.ofSpqrDirection, initInner, spqrDeps, hb,
      SpqrApiResult.ofPanic, topBytes, topPb, vnOf, dparams]
    rfl

/-- `spqrV1Init` produces a serialized state satisfying `PartyTop` at chain epoch `0` with zero
counters. -/
theorem top_init (F : ShaCompress) (K : MlKem) (spqrdir : SpqrDirection) (k : BitVec 256)
    (secret : ℕ → Bytes) (st : St F)
    (hst : initStates F (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir) =
      .ok st) :
    PartyTop F K (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir) secret st 0
      (fun _ => 0) (fun _ => ∅) (spqrV1Init F K spqrdir k) := by
  obtain ⟨hbytes, hep, hcur_st⟩ := dti_initStates_facts F K spqrdir k st hst
  obtain ⟨chE, hvn_ok, hok⟩ :=
    chainFromVN_ok F (CryptoGames.HMAC.keyToBytes32 k) (Direction.ofSpqrDirection spqrdir)
      Version.v1.toI32 secret (fun _ => 0) (fun _ => ∅) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨hcur_ch, hsend_ch⟩ :=
    chainFromVN_fresh F (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)
      chE hvn_ok
  refine ⟨some (vnOf (Direction.ofSpqrDirection spqrdir) (CryptoGames.HMAC.keyToBytes32 k)),
    none, chE, ?_⟩
  refine
    { hbytes := hbytes
      hvn := Or.inr rfl
      hch := Or.inr ⟨rfl, rfl, hvn_ok⟩
      hok := hok
      hcur := by rw [hcur_ch, hcur_st]; rfl
      hsendEp := by rw [hsend_ch]; rfl
      hsendLe := by omega
      hsendPrev := chainFromVN_sendPrevNil F _ _ chE hvn_ok }

private theorem dts_msgBytes_check (m : Msg) (idx : BitVec 32) {α : Type} (x : Except SpqrApiError α) :
    (match Message.serialize m idx with
     | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
     | b0 :: _ =>
       if (b0 != Version.v1.toU8) = true then
         Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
       else x) = x := by
  obtain ⟨rest, hser⟩ := serialize_head m idx
  rw [hser]
  rfl

private theorem dts_keyAt_isEmpty (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    (keyAt F seed n).isEmpty = false := by
  have hlen := length_keyAt F seed n
  rcases h : keyAt F seed n with _ | ⟨_, _⟩
  · rw [h] at hlen; simp at hlen
  · rfl

private theorem dts_messageKeyToSalt_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    messageKeyToSalt? (some (keyAt F seed n)) =
      some (some ⟨keyAt F seed n, length_keyAt F seed n⟩) := by
  simp [messageKeyToSalt?, length_keyAt]

private theorem dts_spqrDeps_msgEpoch (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).msgEpoch = Message.epoch := rfl

private theorem dts_spqrDeps_msgSerialize (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).msgSerialize = Message.serialize := rfl

private theorem dts_spqrDeps_statesIntoPb (F : ShaCompress) (K : MlKem) :
    (spqrDeps F K).statesIntoPb = States.into_pb := rfl

private theorem dts_sendAfterStates_ok (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (chE chain1 chain2 : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (m : Msg) (key : Option EpochSecret)
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1)
    (he_ne0 : (m.epoch == 0#64) = false)
    (idx : BitVec 32) (n : ℕ) (seed : Bytes)
    (hsk : chain1.sendKey (spqrHkdfWith F) (m.epoch - 1#64) = .ok (chain2, (idx, keyAt F seed n))) :
    sendAfterStates (spqrDeps F K) (spqrHkdfWith F) (topPb st vn? ch?) m key st' =
      .ok {
        state := topBytes F K st' vn? (some chain2)
        msg := Message.serialize m idx
        key := some (keyAt F seed n)
      } := by
  have hfp := chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  have hslt : BitVec.slt Version.v0.toI32 (vnOf dir authKey).minVersion = true := rfl
  cases key with
  | none =>
    cases hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp only [sendAfterStates, topBytes, topPb, Option.map,
        dts_spqrDeps_msgEpoch, dts_spqrDeps_msgSerialize, dts_spqrDeps_statesIntoPb,
        hfp, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
        dts_keyAt_isEmpty]
      exact dts_msgBytes_check m idx _
    · simp only [sendAfterStates, topBytes, topPb, Option.map,
        dts_spqrDeps_msgEpoch, dts_spqrDeps_msgSerialize, dts_spqrDeps_statesIntoPb,
        hslt, hvnE, he_ne0, hsk, SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
        dts_keyAt_isEmpty]
      exact dts_msgBytes_check m idx _
  | some es =>
    dsimp only at hadd
    rcases hch with rfl | ⟨rfl, rfl, hvnE⟩
    · simp only [sendAfterStates, topBytes, topPb, Option.map,
        dts_spqrDeps_msgEpoch, dts_spqrDeps_msgSerialize, dts_spqrDeps_statesIntoPb,
        hfp, hadd, he_ne0, hsk,
        SpqrApiResult.ofError, SpqrApiResult.ofChainPanic, SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
        dts_keyAt_isEmpty]
      exact dts_msgBytes_check m idx _
    · simp only [sendAfterStates, topBytes, topPb, Option.map,
        dts_spqrDeps_msgEpoch, dts_spqrDeps_msgSerialize, dts_spqrDeps_statesIntoPb,
        hslt, hvnE, hadd, he_ne0, hsk,
        SpqrApiResult.ofError, SpqrApiResult.ofChainPanic, SpqrApiResult.ofChainResult,
        bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
        dts_keyAt_isEmpty]
      exact dts_msgBytes_check m idx _

private theorem dts_send_addEpoch (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (chE : Chain) (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (tape tape' : Bytes) (m : Msg) (key : Option EpochSecret)
    (hsendB : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape'))
    (hsec : ∀ es, key = some es → es.secret = secret es.epoch.toNat) :
    ∃ chain1 : Chain,
      (match key with
       | some es => chE.addEpoch (spqrHkdfWith F) es
       | none => .ok chE) = .ok chain1 ∧
      ChainOk F authKey dir secret sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      chainCur st ≤ chain1.currentEpoch.toNat := by
  cases key with
  | none =>
    have hc := chainCur_send_none F K st st' tape tape' m hsendB
    exact ⟨chE, rfl, hok, by rw [hcur, hc], rfl, by omega⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_send_key F K st st' tape tape' m es hep_pos hsendB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hsec' : es.secret = secret (chE.currentEpoch.toNat + 1) := by
      rw [hsec es rfl, hep]
    obtain ⟨ch1, hadd, hcur1, hsend1, hok1⟩ :=
      addEpoch_ok F authKey dir secret sendCtr recvSet chE hok es hep hsec'
    refine ⟨ch1, hadd, hok1, ?_, hsend1, ?_⟩
    · rw [hcur1, hes_ep, hc']
    · rw [hcur1, hes_ep]; omega

/-- `LibsignalSpqrV1.send` on a `PartyTop` state emits the next key `keyAt` of chain epoch
`st.epoch - 1`, serializes the wire message with index `sendCtr (st.epoch - 1) + 1`, and preserves
`PartyTop`. -/
theorem top_send (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st st' : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hsize : bytes.length < 2 ^ 64)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st)
    (tape tape' : Bytes) (m : Msg) (key : Option EpochSecret)
    (hsendB : st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape'))
    (hsec : ∀ es, key = some es → es.secret = secret es.epoch.toNat)
    (hctr : sendCtr (st.epoch.toNat - 1) + 1 < 2 ^ 32) :
    ∃ bytes',
      (spqrV1 F K).send bytes tape =
        some (bytes',
          some ⟨keyAt F (seedAt F authKey secret dir (st.epoch.toNat - 1))
              (sendCtr (st.epoch.toNat - 1)), length_keyAt _ _ _⟩,
          Message.serialize m (BitVec.ofNat 32 (sendCtr (st.epoch.toNat - 1) + 1))) ∧
      PartyTop F K authKey dir secret st' (st.epoch.toNat - 1)
        (Function.update sendCtr (st.epoch.toNat - 1) (sendCtr (st.epoch.toNat - 1) + 1))
        recvSet bytes' := by
  have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos h
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  obtain ⟨hm_ep, hst'_ep, -, -⟩ := send_facts F K st st' tape tape' m key hsendB
  have hsize' : (topBytes F K st vn? ch?).length < 2 ^ 64 := hw.hbytes ▸ hsize
  have htop := send_topBytes F K st st' vn? ch? tape tape' m key hsize' hcodec hsendB
  obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
    dts_send_addEpoch F K authKey dir secret st st' sendCtr recvSet chE hw.hok
      hw.hcur hep_pos tape tape' m key hsendB hsec
  have he_ne0 : (m.epoch == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    rw [hm_ep] at this
    omega
  have hebv_nat : (m.epoch - 1#64).toNat = st.epoch.toNat - 1 := by
    rw [hm_ep, BitVec.toNat_sub_of_le]
    · rfl
    · show 1 ≤ st.epoch.toNat
      exact hep_pos
  have hlo : chain1.sendEpoch.toNat ≤ (m.epoch - 1#64).toNat := by
    rw [hsend1, hw.hsendEp, hebv_nat]
    have := hw.hsendLe
    omega
  have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
    rw [hebv_nat]
    exact (epoch_sub_one_le_chainCur st).trans hle1
  have hn : sendCtr (m.epoch - 1#64).toNat + 1 < 2 ^ 32 := by
    rw [hebv_nat]
    exact hctr
  obtain ⟨chain2, hsk, hcur2, hsend2, hok2⟩ :=
    sendKey_ok F authKey dir secret sendCtr recvSet chain1 hok1 (m.epoch - 1#64) hlo hhi hn
  rw [hebv_nat] at hsk hok2
  have hafter := dts_sendAfterStates_ok F K authKey dir secret st st' sendCtr recvSet vn? ch?
    chE chain1 chain2 hw.hch hw.hok m key hadd he_ne0
    (BitVec.ofNat 32 (sendCtr (st.epoch.toNat - 1) + 1))
    (sendCtr (st.epoch.toNat - 1))
    (seedAt F authKey secret dir (st.epoch.toNat - 1)) hsk
  refine ⟨topBytes F K st' vn? (some chain2), ?_, ?_⟩
  · rw [spqrV1_eq, toSpqrModel]
    dsimp only
    rw [hw.hbytes, htop, hafter]
    dsimp only
    rw [dts_messageKeyToSalt_keyAt]
  · have hsp1 := dsp_addEpoch_opt (spqrHkdfWith F) chE chain1 key hw.hsendPrev hadd
    refine ⟨vn?, some chain2, chain2, rfl, hw.hvn, .inl rfl, hok2, ?_, ?_, ?_, ?_⟩
    · rw [hcur2, hcur1]
    · rw [hsend2, hebv_nat]
    · rw [hst'_ep]; omega
    · exact sendKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ hsp1 hsk

private theorem dtr_recv_epoch_le (F : ShaCompress) (K : MlKem) (st st' : St F) (m : Msg)
    (key : Option EpochSecret) (h : st.recv K m = .ok { key := key, state := st' }) :
    st.epoch.toNat ≤ st'.epoch.toNat := by
  obtain ⟨-, ⟨-, ⟨he, -⟩ | ⟨he, -⟩⟩ | ⟨_, -, -, he, -⟩⟩ := recv_facts F K st st' m key h
  · rw [he]
  · omega
  · omega

private theorem dtr_chainFrom_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE) :
    chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) vn? = .ok chE := by
  rcases hch with rfl | ⟨rfl, rfl, hvn⟩
  · exact chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  · exact hvn

private theorem dtr_spqrDeps_statesFromPb (F : ShaCompress) (K : MlKem) (st : St F)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st) :
    (spqrDeps F K).statesFromPb st.into_pb = .ok st := by
  simp only [spqrDeps, hcodec, liftStatesResult]

private theorem dtr_spqrDeps_statesRecv (F : ShaCompress) (K : MlKem) (st st' : St F)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' }) :
    (spqrDeps F K).statesRecv st m = .ok (key, st') := by
  simp only [spqrDeps, hrecvB]

private theorem dtr_recvKeyToSalt_keyAt (F : ShaCompress) (seed : Bytes) (n : ℕ) :
    recvKeyToSalt? (some (keyAt F seed n)) =
      some (some ⟨keyAt F seed n, length_keyAt F seed n⟩) := by
  rw [recvKeyToSalt?_of_isSome]
  · exact dts_messageKeyToSalt_keyAt F seed n
  · rw [dts_messageKeyToSalt_keyAt]; rfl

private theorem dtr_recvEqual_ok (F : ShaCompress) (K : MlKem) (authKey : Bytes)
    (dir : Direction) (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (vn? : Option VersionNegotiationPB) (ch? : Option Chain)
    (chE chain1 chain2 : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st)
    (m : Msg) (key : Option EpochSecret) (rem : Bytes)
    (hdes : (spqrDeps F K).msgDeserialize m.epoch rem = .ok m)
    (hrecvB : st.recv K m = .ok { key := key, state := st' })
    (hadd : (match key with
      | some es => chE.addEpoch (spqrHkdfWith F) es
      | none => .ok chE) = .ok chain1)
    (he_ne0 : (m.epoch == 0#64) = false)
    (idx : BitVec 32) (n : ℕ) (seed : Bytes)
    (hrk : chain1.recvKey (spqrHkdfWith F) (m.epoch - 1#64) idx =
      .ok (chain2, keyAt F seed n)) :
    recvEqual F K st vn? ch? { version := 1#8, epoch := m.epoch, index := idx, remaining := rem } =
      .ok {
        state := topBytes F K st' none (some chain2)
        key := some (keyAt F seed n)
      } := by
  have hcf := dtr_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE hch hok
  have hfpb := dtr_spqrDeps_statesFromPb F K st hcodec
  have hsr := dtr_spqrDeps_statesRecv F K st st' m key hrecvB
  cases key with
  | none =>
    cases hadd
    simp only [recvEqual, topBytes, topPb,
      dts_spqrDeps_statesIntoPb, hdes, hfpb, hsr, he_ne0, hcf, hrk,
      SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
      bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ↓reduceIte,
      dts_keyAt_isEmpty]
    rfl
  | some es =>
    dsimp only at hadd
    simp only [recvEqual, topBytes, topPb,
      dts_spqrDeps_statesIntoPb, hdes, hfpb, hsr, he_ne0, hcf, hadd, hrk,
      SpqrApiResult.ofError, SpqrApiResult.ofChainPanic, SpqrApiResult.ofChainResult,
      bind, Except.bind, Bool.false_eq_true, ↓reduceIte,
      dts_keyAt_isEmpty]
    rfl

private theorem dtr_recv_addEpoch (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st st' : St F) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (chE : Chain) (hok : ChainOk F authKey dir secret sendCtr recvSet chE)
    (hcur : chE.currentEpoch.toNat = chainCur st) (hep_pos : 1 ≤ st.epoch.toNat)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' })
    (hsec : ∀ es, key = some es → es.secret = secret es.epoch.toNat) :
    ∃ chain1 : Chain,
      (match key with
       | some es => chE.addEpoch (spqrHkdfWith F) es
       | none => .ok chE) = .ok chain1 ∧
      ChainOk F authKey dir secret sendCtr recvSet chain1 ∧
      chain1.currentEpoch.toNat = chainCur st' ∧
      chain1.sendEpoch = chE.sendEpoch ∧
      chainCur st ≤ chain1.currentEpoch.toNat := by
  cases key with
  | none =>
    have hc := chainCur_recv_none F K st st' m hep_pos hrecvB
    exact ⟨chE, rfl, hok, by rw [hcur, hc], rfl, by omega⟩
  | some es =>
    obtain ⟨hes_ep, hc'⟩ := chainCur_recv_key F K st st' m es hep_pos hrecvB
    have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by omega
    have hsec' : es.secret = secret (chE.currentEpoch.toNat + 1) := by
      rw [hsec es rfl, hep]
    obtain ⟨ch1, hadd, hcur1, hsend1, hok1⟩ :=
      addEpoch_ok F authKey dir secret sendCtr recvSet chE hok es hep hsec'
    refine ⟨ch1, hadd, hok1, ?_, hsend1, ?_⟩
    · rw [hcur1, hes_ep, hc']
    · rw [hcur1, hes_ep]; omega

/-- `LibsignalSpqrV1.recv` on a `PartyTop` state and an honest in-window message of epoch `E`
and index `idx` (with `idx + 2000 ≤ 2 ^ 32` and `(recvSet (E - 1)).sup id + 2000 ≤ 2 ^ 32`) returns
the sender's key and preserves `PartyTop`. -/
theorem top_recv (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st st' : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hsize : bytes.length < 2 ^ 64)
    (hcodec : States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st)
    (m : Msg) (key : Option EpochSecret)
    (hrecvB : st.recv K m = .ok { key := key, state := st' })
    (hsec : ∀ es, key = some es → es.secret = secret es.epoch.toNat)
    (hpay : m.payload ≠ .ct1Ack false)
    (hE1 : 1 ≤ m.epoch.toNat) (hEcur : m.epoch.toNat ≤ chainCur st + 1)
    (hsendE : sendEp ≤ m.epoch.toNat)
    (idx : ℕ) (hidx : 1 ≤ idx) (hnew : idx ∉ recvSet (m.epoch.toNat - 1))
    (hjump : (recvSet (m.epoch.toNat - 1)).sup id < idx →
      idx - (recvSet (m.epoch.toNat - 1)).sup id ≤ 25000)
    (htrim : idx < (recvSet (m.epoch.toNat - 1)).sup id →
      (recvSet (m.epoch.toNat - 1)).sup id ≤ idx + 2000)
    (hb : idx + 2000 ≤ 2 ^ 32) (hR : (recvSet (m.epoch.toNat - 1)).sup id + 2000 ≤ 2 ^ 32) :
    ∃ bytes',
      (spqrV1 F K).recv bytes (Message.serialize m (BitVec.ofNat 32 idx)) =
        .ok (bytes',
          some ⟨keyAt F (seedAt F authKey secret dir.switch (m.epoch.toNat - 1)) (idx - 1),
            length_keyAt _ _ _⟩) ∧
      PartyTop F K authKey dir secret st' sendEp sendCtr
        (Function.update recvSet (m.epoch.toNat - 1) (insert idx (recvSet (m.epoch.toNat - 1))))
        bytes' := by
  have hep_pos : 1 ≤ st.epoch.toNat := partyTop_epoch_pos h
  have hep_le : st.epoch.toNat ≤ st'.epoch.toNat := dtr_recv_epoch_le F K st st' m key hrecvB
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  have hsize' : (topBytes F K st vn? ch?).length < 2 ^ 64 := hw.hbytes ▸ hsize
  have he_ne : m.epoch ≠ 0#64 := by
    intro h0
    have : m.epoch.toNat = 0 := congrArg BitVec.toNat h0
    omega
  have he_ne0 : (m.epoch == 0#64) = false := beq_eq_false_iff_ne.mpr he_ne
  obtain ⟨rem, hpre, hdes⟩ := msg_roundtrip F K m (BitVec.ofNat 32 idx) he_ne hpay
  have htop :=
    recv_topBytes F K authKey dir st vn? ch? (Message.serialize m (BitVec.ofNat 32 idx))
      { version := 1#8, epoch := m.epoch, index := BitVec.ofNat 32 idx, remaining := rem }
      hsize' hw.hvn hpre rfl
  obtain ⟨chain1, hadd, hok1, hcur1, hsend1, hle1⟩ :=
    dtr_recv_addEpoch F K authKey dir secret st st' sendCtr recvSet chE hw.hok
      hw.hcur hep_pos m key hrecvB hsec
  have hebv_nat : (m.epoch - 1#64).toNat = m.epoch.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · show 1 ≤ m.epoch.toNat
      exact hE1
  have hlo : chain1.sendEpoch.toNat - 1 ≤ (m.epoch - 1#64).toNat := by
    rw [hsend1, hw.hsendEp, hebv_nat]
    omega
  have hhi : (m.epoch - 1#64).toNat ≤ chain1.currentEpoch.toNat := by
    rw [hebv_nat]
    omega
  obtain ⟨chain2, hrk, hcur2, hsend2, hok2⟩ :=
    recvKey_ok F authKey dir secret sendCtr recvSet chain1 hok1 (m.epoch - 1#64) idx
      hlo hhi hidx (hebv_nat ▸ hnew) (hebv_nat ▸ hjump) (hebv_nat ▸ htrim) hb (hebv_nat ▸ hR)
  rw [hebv_nat] at hrk hok2
  have heq := dtr_recvEqual_ok F K authKey dir secret st st' sendCtr recvSet vn? ch?
    chE chain1 chain2 hw.hch hw.hok hcodec m key rem hdes hrecvB hadd he_ne0
    (BitVec.ofNat 32 idx) (idx - 1)
    (seedAt F authKey secret dir.switch (m.epoch.toNat - 1)) hrk
  refine ⟨topBytes F K st' none (some chain2), ?_, ?_⟩
  · rw [spqrV1_eq, toSpqrModel]
    dsimp only
    rw [hw.hbytes, htop, heq]
    dsimp only
    rw [dtr_recvKeyToSalt_keyAt]
  · have hsendLe := hw.hsendLe
    have hsp1 := dsp_addEpoch_opt (spqrHkdfWith F) chE chain1 key hw.hsendPrev hadd
    refine ⟨none, some chain2, chain2, rfl, .inl rfl, .inl rfl, hok2, ?_, ?_, ?_, ?_⟩
    · rw [hcur2, hcur1]
    · rw [hsend2, hsend1, hw.hsendEp]
    · omega
    · exact recvKey_sendPrevNil (spqrHkdfWith F) chain1 chain2 _ _ _ hsp1 hrk

private theorem dte_chainFrom_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE) :
    chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) vn? = .ok chE := by
  rcases hch with rfl | ⟨rfl, rfl, hvn⟩
  · exact chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  · exact hvn

private theorem dte_addEpoch_inv (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (chE chain1 : Chain)
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE) (es : EpochSecret)
    (hadd : chE.addEpoch (spqrHkdfWith F) es = .ok chain1) :
    ∃ secret1, ChainOk F authKey dir secret1 sendCtr recvSet chain1 ∧
      chain1.sendEpoch = chE.sendEpoch := by
  have hadd0 := hadd
  unfold Chain.addEpoch at hadd
  split_ifs at hadd with hovf hmis
  have hcur_lt : chE.currentEpoch.toNat + 1 < 2 ^ 64 := by
    have hlt := chE.currentEpoch.isLt
    have hne : chE.currentEpoch.toNat ≠ 2 ^ 64 - 1 := by
      intro heq
      apply hovf
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      change chE.currentEpoch.toNat = 18446744073709551615
      omega
    omega
  have hep_eq : es.epoch = chE.currentEpoch + 1#64 := by
    simpa [bne_iff_ne] using hmis
  have hep : es.epoch.toNat = chE.currentEpoch.toNat + 1 := by
    rw [hep_eq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcur_lt]
  let secret1 : ℕ → Bytes := Function.update secret (chE.currentEpoch.toNat + 1) es.secret
  have hok1 : ChainOk F authKey dir secret1 sendCtr recvSet chE :=
    chainOk_congr F authKey dir secret secret1 sendCtr recvSet chE hok
      (fun e _ he => Function.update_of_ne (by omega) _ _)
  obtain ⟨ch', hadd', _, hsend', hok'⟩ :=
    addEpoch_ok F authKey dir secret1 sendCtr recvSet chE hok1 es hep
      (Function.update_self (chE.currentEpoch.toNat + 1) es.secret secret).symm
  rw [hadd0] at hadd'
  cases hadd'
  exact ⟨secret1, hok', hsend'⟩

/-- `LibsignalSpqrV1.recv` rejects any version-1 message whose epoch or index violates the
symmetric-chain replay, jump, or trim window bounds. -/
theorem top_recv_err (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hsize : bytes.length < 2 ^ 64)
    (msgBytes : Bytes) (pre : MsgPreamble) (hpre : msgPreamble msgBytes = .ok pre)
    (hver : pre.version = 1#8) (hE1 : 1 ≤ pre.epoch.toNat) (hidx : 1 ≤ pre.index.toNat)
    (hout : pre.epoch.toNat < sendEp ∨
      pre.index.toNat ∈ recvSet (pre.epoch.toNat - 1) ∨
      ((recvSet (pre.epoch.toNat - 1)).sup id < pre.index.toNat ∧
        25000 < pre.index.toNat - (recvSet (pre.epoch.toNat - 1)).sup id) ∨
      (pre.index.toNat < (recvSet (pre.epoch.toNat - 1)).sup id ∧
        pre.index.toNat + 2000 < (recvSet (pre.epoch.toNat - 1)).sup id)) :
    ∀ r, (spqrV1 F K).recv bytes msgBytes ≠ .ok r := by
  intro r hok_recv
  obtain ⟨vn?, ch?, chE, hw⟩ := h
  rw [hw.hbytes] at hsize hok_recv
  rw [spqrV1_eq] at hok_recv
  dsimp [toSpqrModel] at hok_recv
  rw [recv_topBytes F K authKey dir st vn? ch? msgBytes pre hsize hw.hvn hpre hver] at hok_recv
  suffices hne : ∀ rv, recvEqual F K st vn? ch? pre ≠ .ok rv by
    cases hrv : recvEqual F K st vn? ch? pre with
    | error e =>
      rw [hrv] at hok_recv
      cases e <;> contradiction
    | ok rv =>
      exact hne rv hrv
  intro rv hrv
  unfold recvEqual at hrv
  cases hdes : (spqrDeps F K).msgDeserialize pre.epoch pre.remaining with
  | error e =>
    rw [hdes] at hrv
    contradiction
  | ok sckaMsg =>
    rw [hdes] at hrv
    dsimp [bind, Except.bind] at hrv
    cases hfpb : (spqrDeps F K).statesFromPb st.into_pb with
    | error e =>
      rw [hfpb] at hrv
      contradiction
    | ok st0 =>
      rw [hfpb] at hrv
      dsimp [bind, Except.bind] at hrv
      cases hsr : (spqrDeps F K).statesRecv st0 sckaMsg with
      | error e =>
        rw [hsr] at hrv
        contradiction
      | ok ks =>
        rcases ks with ⟨key, st1⟩
        rw [hsr] at hrv
        dsimp [bind, Except.bind] at hrv
        split_ifs at hrv with hep0
        have hcf := dte_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE hw.hch hw.hok
        rw [hcf] at hrv
        obtain ⟨chain1, secret1, hok1, hsend1, cm, hrk⟩ :
            ∃ chain1 secret1, ChainOk F authKey dir secret1 sendCtr recvSet chain1 ∧
              chain1.sendEpoch = chE.sendEpoch ∧
              ∃ cm, chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok cm := by
          cases key with
          | none =>
            dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainResult, pure, Except.pure, bind, Except.bind] at hrv
            cases hrk : chE.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
            | error ce => rw [hrk] at hrv; contradiction
            | ok cm => exact ⟨chE, secret, hw.hok, rfl, cm, hrk⟩
          | some es =>
            dsimp [SpqrApiResult.ofError, SpqrApiResult.ofChainPanic, SpqrApiResult.ofChainResult, bind, Except.bind] at hrv
            cases hadd : chE.addEpoch (spqrHkdfWith F) es with
            | error p => rw [hadd] at hrv; contradiction
            | ok chain1 =>
              rw [hadd] at hrv
              dsimp at hrv
              cases hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index with
              | error ce => rw [hrk] at hrv; contradiction
              | ok cm =>
                obtain ⟨secret1, hok1, hsend1⟩ :=
                  dte_addEpoch_inv F authKey dir secret sendCtr recvSet chE chain1 hw.hok es hadd
                exact ⟨chain1, secret1, hok1, hsend1, cm, hrk⟩
        have hep_sub : (pre.epoch - 1#64).toNat = pre.epoch.toNat - 1 := by
          rw [BitVec.toNat_sub_of_le]
          · rfl
          · change (1#64 : BitVec 64).toNat ≤ pre.epoch.toNat
            exact hE1
        have hsend1_eq : chain1.sendEpoch.toNat = sendEp := by
          rw [hsend1, hw.hsendEp]
        have hout1 : (pre.epoch - 1#64).toNat + 1 < chain1.sendEpoch.toNat ∨
            chain1.currentEpoch.toNat < (pre.epoch - 1#64).toNat ∨
            pre.index.toNat ∈ recvSet (pre.epoch - 1#64).toNat ∨
            ((recvSet (pre.epoch - 1#64).toNat).sup id < pre.index.toNat ∧
              25000 < pre.index.toNat - (recvSet (pre.epoch - 1#64).toNat).sup id) ∨
            (pre.index.toNat < (recvSet (pre.epoch - 1#64).toNat).sup id ∧
              pre.index.toNat + 2000 < (recvSet (pre.epoch - 1#64).toNat).sup id) := by
          rw [hep_sub, hsend1_eq]
          rcases hout with h1 | h2 | h3 | h4
          · exact Or.inl (by omega)
          · exact Or.inr (Or.inr (Or.inl h2))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
        have herr := recvKey_err F authKey dir secret1 sendCtr recvSet chain1 hok1
          (pre.epoch - 1#64) pre.index.toNat hidx pre.index.isLt hout1
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at herr
        exact herr cm hrk

end CryptoVerification.SpqrV1Sync.TopSync
