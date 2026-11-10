/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import LibsignalBinary.Proofs.SpqrV1Sync.Codec.StatesPb
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Encaps1Total

/-!
# SPQR V1 Send Totality Definitions and Reduction

Defines the single-party SPQR V1 state invariant `TopAdv` (with explicit witness record `TopAdvW`)
under `n < q < 2 ^ 32` own sends and arbitrary adversarial receives, states the component proof
obligations (`TopStmts` and braid/erasure/chain sub-obligations), and reduces bounded send totality
(`sendCorrectQ_of`) to `TopStmts` under `Encaps1Total`.

Key design choices:
- **Send budget `q < 2 ^ 32`**: without receives, a party remains in epoch `0` and its send counter
  equals `n`, overflowing `u32::MAX` on send `2 ^ 32`. Bounding `n < q < 2 ^ 32` keeps all send
  counters below `2 ^ 32 - 1` and limits the chain to at most `n + 2` links via the braid potential
  `phiB`.
- **Per-link history bound `RecvSmall`**: adversarial receives can advance an epoch's receive
  counter toward `2 ^ 32` in jumps of `25000`, but `KeyHistory.gc` trims `prev.data` at `2201 * 36`
  bytes down to `≤ 2001` entries, keeping each link's receive history below `2 ^ 20` bytes.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress SpqrDirection)
open CryptoGames.HKDF (Salt)

/-! ## Satisfiability of `Encaps1Total` -/

/-- Constant-output `MlKem` witness showing `Encaps1Total` is non-vacuous. -/
def kTotal : MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ =>
    some (List.Vector.replicate 960 0#8, List.Vector.replicate 2080 0#8,
      List.Vector.replicate 32 0#8)
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 0#8
  validPk := fun _ _ => true

theorem encaps1Total_kTotal : Encaps1Total kTotal := by
  intro _ _ _
  rfl

/-! ## Well-formed braid states -/

/-- Both authenticator keys (`rootKey` and `macKey`) have length `32`. -/
def AuthOk (a : Authenticator) : Prop :=
  a.rootKey.length = 32 ∧ a.macKey.length = 32

/-- Polynomial encoder invariant `Erasure.EncInv` for some `len`-byte message. -/
def EncWF (len : ℕ) (e : PolyEncoder) : Prop :=
  ∃ msg : Bytes, Erasure.EncInv msg e ∧ msg.length = len

/-- Well-formed polynomial decoder for a `2 * n`-byte message under arbitrary chunks: `16` point
sets, each strictly sorted by `x : GF16` (hence at most `2 ^ 16` points per set). -/
def DecWF (n : ℕ) (d : PolyDecoder) : Prop :=
  d.ptsNeeded = n ∧ d.pts.length = 16 ∧
    ∀ j (h : j < d.pts.length), (d.pts[j].vec.map fun pt => pt.x.value.toNat).Pairwise (· < ·)

/-- Well-formed braid state reachable under own sends and adversarial receives: `AuthOk`
authenticators, valid unchunked key/ciphertext lengths (`Codec.UcOk.*`), `EncWF` encoders (`96`,
`1152`, `960`, or `160` bytes), and `DecWF` decoders (`48`, `576`, `480`, or `80` points). -/
def BOk {F : ShaCompress} : St F → Prop
  | .keysUnsampled s => AuthOk s.uc.auth
  | .keysSampled s => AuthOk s.uc.auth ∧ Codec.UcOk.ekHeaderSent s.uc ∧ EncWF 96 s.sending_hdr
  | .headerSent s => AuthOk s.uc.auth ∧ Codec.UcOk.ekEkSent s.uc ∧ EncWF 1152 s.sending_ek ∧
      DecWF 480 s.receiving_ct1
  | .ct1Received s => AuthOk s.uc.auth ∧ Codec.UcOk.ekEkSentCt1Received s.uc ∧
      EncWF 1152 s.sending_ek
  | .ekSentCt1Received s => AuthOk s.uc.auth ∧ Codec.UcOk.ekEkSentCt1Received s.uc ∧
      DecWF 80 s.receiving_ct2
  | .noHeaderReceived s => AuthOk s.uc.auth ∧ DecWF 48 s.receiving_hdr
  | .headerReceived s => AuthOk s.uc.auth ∧ Codec.UcOk.ctHeaderReceived s.uc ∧
      DecWF 576 s.receiving_ek
  | .ct1Sampled s => AuthOk s.uc.auth ∧ Codec.UcOk.ctCt1Sent s.uc ∧ EncWF 960 s.sending_ct1 ∧
      DecWF 576 s.receiving_ek
  | .ekReceivedCt1Sampled s => AuthOk s.uc.auth ∧ Codec.UcOk.ctCt1SentEkReceived s.uc ∧
      EncWF 960 s.sending_ct1
  | .ct1Acknowledged s => AuthOk s.uc.auth ∧ Codec.UcOk.ctCt1Sent s.uc ∧
      DecWF 576 s.receiving_ek
  | .ct2Sampled s => AuthOk s.uc.auth ∧ EncWF 160 s.sending_ct2

/-- The three states that have not sent in their epoch yet (`keysUnsampled`: before `generate`;
`noHeaderReceived` / `headerReceived`: before `encaps1`). -/
def freshB {F : ShaCompress} : St F → Bool
  | .keysUnsampled _ | .noHeaderReceived _ | .headerReceived _ => true
  | _ => false

/-- Braid send potential `epoch - 1 + (0 if freshB else 1)`, bounding `phiB st ≤ n` after `n` own
sends and arbitrary receives. -/
def phiB {F : ShaCompress} (st : St F) : ℕ :=
  st.epoch.toNat - 1 + (if freshB st then 0 else 1)

/-- The active chain epoch `chainCur st` never exceeds the braid send potential `phiB st`. -/
theorem chainCur_le_phiB {F : ShaCompress} (st : St F) : chainCur st ≤ phiB st := by
  cases st <;> simp [chainCur, phiB, keyedB, freshB]
/-- Every chain link's receive history `l.recv.prev.data` has fewer than `2 ^ 20` bytes. -/
def RecvSmall (ch : Chain) : Prop :=
  ∀ l ∈ ch.links, l.recv.prev.data.length < 2 ^ 20

/-! ## Single-party reachability invariant -/

/-- Explicit-witness single-party state invariant after `n` own sends and arbitrary adversarial
receives: serialized `PartyTopW` state, 32-byte `authKey`, `BOk` braid state, `phiB` and send
counters bounded by `n`, and `RecvSmall` chain history. -/
structure TopAdvW (F : ShaCompress) (K : MlKem) (n : ℕ) (bytes authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain) : Prop where
  htop : PartyTopW F K authKey dir secret st sendEp sendCtr recvSet bytes vn? ch? chE
  hauth : authKey.length = 32
  hbok : BOk st
  hphi : phiB st ≤ n
  hctr : ∀ e, sendCtr e ≤ n
  hsmall : RecvSmall chE

/-- Existentially quantified single-party state invariant (`TopAdvW` for some witnesses). -/
def TopAdv (F : ShaCompress) (K : MlKem) (n : ℕ) (bytes : Bytes) : Prop :=
  ∃ authKey dir secret st sendEp sendCtr recvSet vn? ch? chE,
    TopAdvW F K n bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE

/-! ## Top-level statements -/

/-- `spqrV1Init` establishes `TopAdv` at `0` sends. -/
def TopInitStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (spqrdir : SpqrDirection) (k : BitVec 256), TopAdv F K 0 (spqrV1Init F K spqrdir k)

/-- Below `2 ^ 32 - 1` sends and given `Encaps1Total` and a 64-byte RNG tape, `(spqrV1 F K).send`
succeeds on any `TopAdv` state. -/
def TopTotalStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (n : ℕ) (bytes tape : Bytes), TopAdv F K n bytes → n + 1 < 2 ^ 32 → Encaps1Total K →
    64 ≤ tape.length → ((spqrV1 F K).send bytes tape).isSome

/-- `(spqrV1 F K).send` advances `TopAdv n` to `TopAdv (n + 1)` when `n + 1 < 2 ^ 32`. -/
def TopSendClosedStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (n : ℕ) (bytes tape bytes' : Bytes) (salt : Salt) (msg : Bytes), TopAdv F K n bytes →
    n + 1 < 2 ^ 32 → (spqrV1 F K).send bytes tape = some (bytes', salt, msg) →
    TopAdv F K (n + 1) bytes'

/-- `(spqrV1 F K).recv` on any adversarial message preserves `TopAdv n` when `n < 2 ^ 32`. -/
def TopRecvClosedStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (n : ℕ) (bytes msg bytes' : Bytes) (salt : Salt), TopAdv F K n bytes → n < 2 ^ 32 →
    (spqrV1 F K).recv bytes msg = .ok (bytes', salt) → TopAdv F K n bytes'

/-- Version-1 (`Ordering::Equal`) branch of `Top.recv`: `recvEqual` preserves `TopAdv n`. -/
def TopRecvEqualStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (n : ℕ) (bytes authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (st : St F)
    (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (vn? : Option VersionNegotiationPB)
    (ch? : Option Chain) (chE : Chain) (pre : MsgPreamble) (r : Recv),
    TopAdvW F K n bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE → n < 2 ^ 32 →
    recvEqual F K st vn? ch? pre = .ok r → TopAdv F K n r.state

/-- Every `TopAdv n` state with `n < 2 ^ 32` has serialized length `< 2 ^ 64`. -/
def TopSizeStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (n : ℕ) (bytes : Bytes), TopAdv F K n bytes → n < 2 ^ 32 → bytes.length < 2 ^ 64

/-! ## Braid statements -/

/-- `initStates` produces a `BOk` braid state at potential `phiB = 0`. -/
def BInitStmt (F : ShaCompress) : Prop :=
  ∀ (authKey : Bytes) (dir : Direction), authKey.length = 32 →
    ∃ st : St F, initStates F authKey dir = .ok st ∧ BOk st ∧ phiB st = 0

/-- `States.send` increases `phiB` by at most `1` and `States.recv` does not increase `phiB`. -/
def BPhiStmt (F : ShaCompress) (K : MlKem) : Prop :=
  (∀ (st st' : St F) (tape tape' : Bytes) (m : Msg) (key : Option EpochSecret),
    st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape') →
      phiB st' ≤ phiB st + 1) ∧
  (∀ (st st' : St F) (m : Msg) (key : Option EpochSecret),
    st.recv K m = .ok { key := key, state := st' } → phiB st' ≤ phiB st)

/-- On a 64-byte RNG tape under `Encaps1Total`, `States.send` succeeds on any `BOk` braid state. -/
def BSendOkStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (st : St F) (tape : Bytes), BOk st → Encaps1Total K → 64 ≤ tape.length →
    ∃ (v : V1Send spqrPolyApi (spqrAuthApi F)) (tape' : Bytes), st.send K tape = .ok (v, tape')

/-- `States.send` preserves `BOk`. -/
def BSendClosedStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (st st' : St F) (tape tape' : Bytes) (m : Msg) (key : Option EpochSecret), BOk st →
    st.send K tape = .ok ({ msg := m, key := key, state := st' }, tape') → BOk st'

/-- The EK-side arms of `States` (`Chunked.SendEk`). -/
def isEkSide {F : ShaCompress} : St F → Bool
  | .keysUnsampled _ | .keysSampled _ | .headerSent _ | .ct1Received _
  | .ekSentCt1Received _ => true
  | _ => false

/-- `States.recv` preserves `BOk` on EK-side states. -/
def BRecvEkStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (st st' : St F) (m : Msg) (key : Option EpochSecret), isEkSide st = true → BOk st →
    st.recv K m = .ok { key := key, state := st' } → BOk st'

/-- `States.recv` preserves `BOk` on CT-side states. -/
def BRecvCtStmt (F : ShaCompress) (K : MlKem) : Prop :=
  ∀ (st st' : St F) (m : Msg) (key : Option EpochSecret), isEkSide st = false → BOk st →
    st.recv K m = .ok { key := key, state := st' } → BOk st'

/-- `States.from_pb` inverts `States.into_pb` on any `BOk` state. -/
def BCodecStmt (F : ShaCompress) : Prop :=
  ∀ st : St F, BOk st → States.from_pb spqrPolyApi (spqrAuthApi F) st.into_pb = .ok st

/-! ## Erasure-code statements -/

/-- `PolyDecoder.new` on an even byte length produces a `DecWF (len / 2)` decoder. -/
def DecFreshStmt : Prop :=
  ∀ len : ℕ, len % 2 = 0 → ∃ d, PolyDecoder.new len = .ok (.ok d) ∧ DecWF (len / 2) d

/-- `PolyDecoder.addChunk` preserves `DecWF n` for arbitrary chunks. -/
def DecAddStmt : Prop :=
  ∀ (n : ℕ) (d d' : PolyDecoder) (c : Chunk), DecWF n d → d.addChunk c = .ok d' → DecWF n d'

/-- Any message decoded from a `DecWF n` decoder has length `2 * n`. -/
def DecMsgStmt : Prop :=
  ∀ (n : ℕ) (d : PolyDecoder) (out : Bytes), DecWF n d → d.decodedMessage = .ok (some out) →
    out.length = 2 * n

/-- `PolyEncoder.nextChunk` succeeds and preserves `EncWF len` when `len ≤ 2 ^ 20`. -/
def EncNextStmt : Prop :=
  ∀ (len : ℕ) (e : PolyEncoder), EncWF len e → len ≤ 2 ^ 20 →
    ∃ e' c, e.nextChunk = .ok (e', c) ∧ EncWF len e'

/-- `PolyEncoder.encodeBytes` succeeds and produces an `EncWF` encoder on even messages of length
`≤ 2 ^ 20`. -/
def EncNewStmt : Prop :=
  ∀ msg : Bytes, msg.length % 2 = 0 → msg.length ≤ 2 ^ 20 →
    ∃ e, PolyEncoder.encodeBytes msg = .ok (.ok e) ∧ EncWF msg.length e

/-! ## Chain statements -/

/-- Any successful `ChainEpochDirection.key` on a `RecvDirOk` direction yields a fresh index `≥ 1`,
returns the honest key, and preserves `RecvDirOk`. -/
def RecvDirStmt (F : ShaCompress) : Prop :=
  ∀ (seed : Bytes) (R : Finset ℕ) (d d' : ChainEpochDirection) (idx : BitVec 32) (out : Bytes),
    seed.length = 32 → RecvDirOk F seed R d →
    d.key (spqrHkdfWith F) idx dparams = .ok (d', out) →
    idx.toNat ∉ R ∧ 1 ≤ idx.toNat ∧ out = keyAt F seed (idx.toNat - 1) ∧
      RecvDirOk F seed (insert idx.toNat R) d'

/-- Any successful `ChainEpochDirection.key` on a `RecvDirOk` direction preserves
`prev.data.length < 2 ^ 20`. -/
def RecvPrevStmt (F : ShaCompress) : Prop :=
  ∀ (seed : Bytes) (R : Finset ℕ) (d d' : ChainEpochDirection) (idx : BitVec 32) (out : Bytes),
    seed.length = 32 → RecvDirOk F seed R d → d.prev.data.length < 2 ^ 20 →
    d.key (spqrHkdfWith F) idx dparams = .ok (d', out) → d'.prev.data.length < 2 ^ 20

/-- Any successful `Chain.recvKey` preserves `ChainOk` (for updated receive sets) and `RecvSmall`. -/
def ChainRecvStmt (F : ShaCompress) : Prop :=
  ∀ (authKey : Bytes) (dir : Direction) (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ)
    (recvSet : ℕ → Finset ℕ) (ch ch' : Chain) (e : Epoch) (idx : BitVec 32) (out : Bytes),
    ChainOk F authKey dir secret sendCtr recvSet ch → RecvSmall ch →
    ch.recvKey (spqrHkdfWith F) e idx = .ok (ch', out) →
    ∃ recvSet', ChainOk F authKey dir secret sendCtr recvSet' ch' ∧ RecvSmall ch' ∧
      ch'.currentEpoch = ch.currentEpoch ∧ ch'.sendEpoch = ch.sendEpoch

/-- `chainFromVersionNegotiation` produces a `RecvSmall` chain. -/
def RecvSmallVNStmt (F : ShaCompress) : Prop :=
  ∀ (vn : VersionNegotiationPB) (ch : Chain),
    chainFromVersionNegotiation (spqrHkdfWith F) vn = .ok ch → RecvSmall ch

/-- `Chain.addEpoch` preserves `RecvSmall`. -/
def RecvSmallAddStmt : Prop :=
  ∀ (hkdf : HkdfFn) (ch ch' : Chain) (es : EpochSecret), RecvSmall ch →
    ch.addEpoch hkdf es = .ok ch' → RecvSmall ch'

/-- `Chain.sendKey` preserves `RecvSmall`. -/
def RecvSmallSendStmt : Prop :=
  ∀ (hkdf : HkdfFn) (ch ch' : Chain) (e : Epoch) (out : BitVec 32 × Bytes), RecvSmall ch →
    ch.sendKey hkdf e = .ok (ch', out) → RecvSmall ch'

/-! ## Top-level reduction -/

/-- Bundle of the four top-level SPQR V1 send-totality obligations. -/
structure TopStmts (F : ShaCompress) (K : MlKem) : Prop where
  init : TopInitStmt F K
  total : TopTotalStmt F K
  sendClosed : TopSendClosedStmt F K
  recvClosed : TopRecvClosedStmt F K

/-- Whenever `(spqrV1SessionUniformCoins F K).send` returns `some`, `sendPanics` is `false`. -/
theorem sendPanics_eq_false_of_isSome (F : ShaCompress) (K : MlKem) (st : List (BitVec 8))
    (r : BitVec 512) (h : ((spqrV1SessionUniformCoins F K).send st r).isSome) :
    (spqrV1SessionUniformCoins F K).sendPanics st r = false := by
  simp only [spqrV1SessionUniformCoins, spqrV1_eq, toSpqrModel, sendPanicsPureB] at h ⊢
  cases hres : (CryptoVerification.LibsignalSpqrV1.send (spqrDeps F K) (spqrHkdfWith F) st (coinBytes r)).1 with
  | ok _ => rfl
  | error _ => simp [hres] at h

/-- Bounded send totality for `spqrV1SessionUniformCoins F K` with send budget `q < 2 ^ 32` under
`Encaps1Total K`: `Inv n bytes := n < q → TopAdv F K n bytes` is established by `init`, preserved
by `send` and `recv`, and guarantees `send` returns `some` without panicking for `n < q`. -/
theorem sendCorrectQ_of (F : ShaCompress) (K : MlKem) (h : TopStmts F K) (hK : Encaps1Total K)
    (q : ℕ) (hq : q < 2 ^ 32) :
    ∃ Inv : ℕ → Bytes → Prop,
      (∀ dir k, Inv 0 ((spqrV1SessionUniformCoins F K).init dir k)) ∧
      (∀ n st r st' salt msg, Inv n st → (spqrV1SessionUniformCoins F K).send st r = some (st', salt, msg) →
        Inv (n + 1) st') ∧
      (∀ n st msg st' salt, Inv n st → (spqrV1SessionUniformCoins F K).recv st msg = .ok (st', salt) →
        Inv n st') ∧
      (∀ n st r, n < q → Inv n st → ((spqrV1SessionUniformCoins F K).send st r).isSome) ∧
      (∀ n st r, n < q → Inv n st → (spqrV1SessionUniformCoins F K).sendPanics st r = false) := by
  refine ⟨fun n st => n < q → TopAdv F K n st, ?_, ?_, ?_, ?_, ?_⟩
  · intro dir k _
    exact h.init dir k
  · intro n st r st' salt msg hinv hsend hn1
    exact h.sendClosed n st (coinBytes r) st' salt msg (hinv (by omega)) (by omega) hsend
  · intro n st msg st' salt hinv hrecv hn
    exact h.recvClosed n st msg st' salt (hinv hn) (by omega) hrecv
  · intro n st r hn hinv
    exact h.total n st (coinBytes r) (hinv hn) (by omega) hK (by rw [coinBytes_length])
  · intro n st r hn hinv
    exact sendPanics_eq_false_of_isSome F K st r
      (h.total n st (coinBytes r) (hinv hn) (by omega) hK (by rw [coinBytes_length]))

end CryptoVerification.SpqrV1Sync.SendTotal
