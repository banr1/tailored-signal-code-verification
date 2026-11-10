/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureCode

/-!
# Phase-1 Braid Synchronization Invariant (`InSync1`)

Synchronization invariant `InSync1` for the header-transmission phase of an SPQR V1 braid epoch on
decoded `States spqrPolyApi (spqrAuthApi F)` states:
* The EK side `X_e` starts in `.keysUnsampled` (`seed? = none`), samples a 64-byte ML-KEM seed `s`
  on its first send, and transitions to `.keysSampled` (`seed? = some s`) emitting erasure-coded
  chunks of the 96-byte authenticated header `hdrMsg`.
* The CT side `Y_e` starts in `.noHeaderReceived` with a fresh 96-byte decoder and transitions to
  `.headerReceived` once 3 distinct header chunks arrive and pass `verifyHdr`.
* In-flight sets `toY` and `toX` accumulate all sent messages monotonically, modeling arbitrary
  message drop, reordering, and replay.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.InSync

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoGames.LibsignalSession (ShaCompress)

/-! ## Phase-1 ghost transcript -/

/-- Decoded braid state of `spqrV1`. -/
abbrev St (F : ShaCompress) := States spqrPolyApi (spqrAuthApi F)

/-- Decoded wire message of `spqrV1`. -/
abbrev Msg := Message spqrPolyApi

/-- 64-byte ML-KEM key-generation seed drawn by the EK side in `.keysUnsampled`. -/
abbrev Seed := List.Vector (BitVec 8) 64

/-- ML-KEM public header derived from `s`. -/
def hdrOf (K : MlKem) (s : Seed) : Bytes := (K.fromSeed s).1.toList

/-- ML-KEM encapsulation key derived from `s`. -/
def ekOf (K : MlKem) (s : Seed) : Bytes := (K.fromSeed s).2.1.toList

/-- ML-KEM decapsulation key derived from `s`. -/
def dkOf (K : MlKem) (s : Seed) : Bytes := (K.fromSeed s).2.2.toList

/-- 96-byte authenticated header payload `hdrOf K s ++ auth.macHdrUnchecked F e (hdrOf K s)`. -/
def hdrMsg (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed) : Bytes :=
  hdrOf K s ++ auth.macHdrUnchecked F e (hdrOf K s)

/-- Well-formedness of an `Authenticator` (32-byte MAC key). -/
def AuthWf (auth : Authenticator) : Prop := auth.macKey.length = 32

/-- Initial `PolyDecoder` state returned by `PolyDecoder.new len` for even `len`. -/
def freshDec (len : Nat) : PolyDecoder :=
  { ptsNeeded := len / 2, pts := List.replicate 16 SortedSetPt.new, isComplete := false }

/-- Honest `.hdr` chunk `idx` of `hdrMsg` at epoch `e`. -/
noncomputable def hdrChunkMsg (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (idx : BitVec 16) : Msg where
  epoch := e
  payload := .hdr (spqrPolyApi.mkChunk idx (Erasure.chunkData (hdrMsg F K e auth s) idx))

/-! ## Phase-1 invariant -/

/-- EK-side state invariant in phase 1 (`none` = `.keysUnsampled`, `some s` = `.keysSampled`). -/
def XShape (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) :
    Option Seed → St F → Prop
  | none, x => x = .keysUnsampled { uc := { epoch := e, auth := auth } }
  | some s, x => ∃ enc : PolyEncoder, EncInv (hdrMsg F K e auth s) enc ∧
      x = .keysSampled { uc := { epoch := e, auth := auth, ek := ekOf K s, dk := dkOf K s },
                         sending_hdr := enc }

/-- CT-side state invariant in phase 1 (`3 = needed 96 0` distinct chunks decode `hdrMsg`). -/
def YShape (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) :
    Option Seed → St F → Prop
  | none, y =>
      y = .noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := freshDec 96 }
  | some s, y =>
      (∃ (S : Finset Nat) (dec : PolyDecoder), DecInv (hdrMsg F K e auth s) S dec ∧ S.card < 3 ∧
        y = .noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := dec }) ∨
      y = .headerReceived { uc := { epoch := e, auth := auth, hdr := hdrOf K s },
                            receiving_ek := freshDec 1152 }

/-- Valid phase-1 messages in flight toward `Y_e`: earlier-epoch messages or honest `.hdr` chunks. -/
def ToYOk (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (seed? : Option Seed)
    (m : Msg) : Prop :=
  m.epoch < e ∨
  ∃ s, seed? = some s ∧ ∃ idx : BitVec 16, m = hdrChunkMsg F K e auth s idx

/-- Valid phase-1 messages in flight toward `X_e`: earlier-epoch messages or `.none` at epoch `e`. -/
def ToXOk (e : Epoch) (m : Msg) : Prop :=
  m.epoch < e ∨ m = { epoch := e, payload := .none }

/-- Phase-1 synchronization invariant at epoch `e` with shared `auth` and optional seed `seed?`. -/
structure InSync1 (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg) : Prop where
  hauth : AuthWf auth
  hx : XShape F K e auth seed? x
  hy : YShape F K e auth seed? y
  htoY : ∀ m ∈ toY, ToYOk F K e auth seed? m
  htoX : ∀ m ∈ toX, ToXOk e m

/-! ## Basic properties -/

theorem hdrMsg_length (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed) :
    (hdrMsg F K e auth s).length = 96 := by
  simp [hdrMsg, hdrOf]

theorem decoderNew_eq (len : Nat) (heven : len % 2 = 0) :
    PolyDecoder.new len = .ok (.ok (freshDec len)) := by
  simp [PolyDecoder.new, PolyDecoder.newWithPolyCount, heven, freshDec, pure, Except.pure]

theorem decInv_freshDec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0) :
    DecInv msg ∅ (freshDec msg.length) := by
  obtain ⟨dec, h, hd⟩ := decoderNew_spec msg heven
  rw [decoderNew_eq _ heven] at h
  cases h
  exact hd

/-- `Authenticator.new` produces a 32-byte MAC key (`AuthWf`). -/
theorem authWf_new (F : ShaCompress) (authKey : Bytes) (ep : Epoch) :
    AuthWf (Authenticator.new F authKey ep) := by
  simp [AuthWf, Authenticator.new, Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]

/-- `Authenticator.macHdr` succeeds on a well-formed authenticator and 64-byte header. -/
theorem macHdr_eq (F : ShaCompress) (auth : Authenticator) (hauth : AuthWf auth) (e : Epoch)
    (hdr : Bytes) (hhdr : hdr.length = 64) :
    auth.macHdr F e hdr = .ok (auth.macHdrUnchecked F e hdr) := by
  have hlab : Authenticator.hdrLabel.length = 33 := by decide
  have hbe : (CryptoGames.HMAC.toBEBytes 8 e).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
  apply Authenticator.macHdr_of_lt
  · rw [hauth]; decide
  · simp only [List.length_append, hlab, hbe, hhdr]; decide

/-- `Authenticator.verifyHdrError` accepts the tag computed by `macHdrUnchecked`. -/
theorem verifyHdr_macHdr (F : ShaCompress) (auth : Authenticator) (hauth : AuthWf auth)
    (e : Epoch) (hdr : Bytes) (hhdr : hdr.length = 64) :
    auth.verifyHdrError F e hdr (auth.macHdrUnchecked F e hdr) = .ok (.ok ()) := by
  have hlab : Authenticator.hdrLabel.length = 33 := by decide
  have hbe : (CryptoGames.HMAC.toBEBytes 8 e).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
  have hself : ∀ (l : Bytes) (r : BitVec 8),
      (l.zip l).foldl (fun r (a, b) => r ||| (a ^^^ b)) r = r := by
    intro l; induction l with
    | nil => intro r; rfl
    | cons a l ih => intro r; simp [ih]
  have hmac : (auth.macHdrUnchecked F e hdr).length ≤ 32 := by
    simp [Authenticator.macHdrUnchecked, Authenticator.macSize]
  unfold Authenticator.verifyHdrError
  rw [Authenticator.verifyHdr_eq_ok_prefix F auth e hdr _ (by rw [hauth]; decide)
    (by simp only [List.length_append, hlab, hbe, hhdr]; decide) hmac]
  simp [Authenticator.verifyHdr_prefix, compare_prefix, hself, isNonZero, inz, Except.map,
    Except.mapError]

/-! ## EK-side (`X_e`) transitions -/

namespace XSendUnsampled

theorem generate_eq_match (K : MlKem) (tape : Bytes) :
    generate K tape =
      match (if h : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE
             then some ⟨tape.take KEY_GENERATION_SEED_SIZE, h⟩ else none) with
      | none => .error (.rngExhausted KEY_GENERATION_SEED_SIZE tape.length)
      | some seed =>
        let (hdr, ek, dk) := K.fromSeed seed
        .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList },
          tape.drop KEY_GENERATION_SEED_SIZE) :=
  rfl

end XSendUnsampled

/-- First EK-side send: `.keysUnsampled` draws a 64-byte seed, encodes `hdrMsg`, and emits
chunk `0`. -/
theorem xSend_unsampled (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : AuthWf auth) (x : St F) (hx : XShape F K e auth none x)
    (tape : Bytes) (htape : 64 ≤ tape.length) :
    ∃ s : Seed, s.toList = tape.take 64 ∧ ∃ x' : St F,
      x.send K tape =
        .ok ({ msg := hdrChunkMsg F K e auth s 0#16, key := none, state := x' }, tape.drop 64) ∧
      XShape F K e auth (some s) x' := by
  simp only [XShape] at hx; subst hx
  have h64 : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE := by
    simp only [KEY_GENERATION_SEED_SIZE, List.length_take]; omega
  let s : Seed := ⟨_, h64⟩
  have hgen : generate K tape =
      .ok ({ ek := ekOf K s, dk := dkOf K s, hdr := hdrOf K s }, tape.drop 64) := by
    rw [XSendUnsampled.generate_eq_match]; simp only [h64, ↓reduceDIte]; rfl
  have hmac := macHdr_eq F auth hauth e (hdrOf K s) (by simp [hdrOf])
  have hlen := hdrMsg_length F K e auth s
  have henc := encodeBytes_spec (hdrMsg F K e auth s) (by simp [hlen]) (by simp [hlen])
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (hdrMsg F K e auth s)
      { idx := 0#32, s := .points (msgPoints (hdrMsg F K e auth s)) } (Or.inl rfl) (by simp [hlen])
  have h0 : (0#32).setWidth 16 = 0#16 := by decide
  refine ⟨s, rfl, .keysSampled { uc := { epoch := e, auth := auth, ek := ekOf K s, dk := dkOf K s },
                                 sending_hdr := enc' }, ?_, enc', henc', rfl⟩
  simp only [hdrMsg, h0] at henc hnext
  simp [States.send, Chunked.SendEk.KeysUnsampled.send_hdr_chunk,
    Unchunked.SendEk.KeysUnsampled.send_header, hgen, spqrAuthApi, hmac, expectEncodeBytes,
    spqrPolyApi, henc, hnext, Except.mapError, StatesResult.ofPanic, bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
    Chunked.SendEk.KeysUnsampled.epoch, hdrChunkMsg, hdrMsg]

/-- Subsequent EK-side sends: `.keysSampled` emits the next honest `.hdr` chunk without drawing
coins. -/
theorem xSend_sampled (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (x : St F) (hx : XShape F K e auth (some s) x) (tape : Bytes) :
    ∃ (idx : BitVec 16) (x' : St F),
      x.send K tape =
        .ok ({ msg := hdrChunkMsg F K e auth s idx, key := none, state := x' }, tape) ∧
      XShape F K e auth (some s) x' := by
  obtain ⟨enc, henc, rfl⟩ := hx
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (hdrMsg F K e auth s) enc henc (by rw [hdrMsg_length]; decide)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', henc', rfl⟩
  simp only [States.send, Chunked.SendEk.KeysSampled.send_hdr_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic, Chunked.SendEk.KeysSampled.epoch]
  rfl

/-- `X_e` ignores all valid phase-1 messages in flight toward it. -/
theorem xRecv (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x : St F) (hx : XShape F K e auth seed? x) (m : Msg) (hm : ToXOk e m) :
    x.recv K m = .ok { key := none, state := x } := by
  have hle : ¬ e < m.epoch := by
    rcases hm with h | h
    · simp only [BitVec.lt_def] at h ⊢; omega
    · subst h; exact BitVec.lt_irrefl _
  cases seed? with
  | none =>
    simp only [XShape] at hx; subst hx
    simp [States.recv, Chunked.SendEk.KeysUnsampled.epoch, hle]
  | some s =>
    obtain ⟨enc, -, rfl⟩ := hx
    rcases hm with h | rfl
    · simp [States.recv, Chunked.SendEk.KeysSampled.epoch, hle, h]
    · simp [States.recv, Chunked.SendEk.KeysSampled.epoch]

/-! ## CT-side (`Y_e`) transitions -/

/-- Before `.headerReceived`, `Y_e` sends `.none` and leaves its state unchanged. -/
theorem ySend_noHeader (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (y : St F) (hy : YShape F K e auth seed? y)
    (hnhr : ∀ s, y ≠ .headerReceived s) (tape : Bytes) :
    y.send K tape =
      .ok ({ msg := { epoch := e, payload := .none }, key := none, state := y }, tape) := by
  cases seed? with
  | none => simp only [YShape] at hy; subst hy; rfl
  | some s =>
    rcases hy with ⟨S, dec, -, -, rfl⟩ | rfl
    · rfl
    · exact absurd rfl (hnhr _)

namespace YSendHeaderReceived

theorem encaps1_eq_match (K : MlKem) (hdr : Header) (tape : Bytes) :
    encaps1 K hdr tape =
      match (if h1 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE
             then some ⟨tape.take SHARED_SECRET_SIZE, h1⟩ else none) with
      | none => .error (.rngExhausted SHARED_SECRET_SIZE tape.length)
      | some rand =>
        match K.encaps1 hdr rand with
        | none => .error .encaps1Failed
        | some (ct1, es, ss) =>
          .ok ((ct1.toList, es.toList, ss.toList), tape.drop SHARED_SECRET_SIZE) :=
  rfl

end YSendHeaderReceived

/-- Phase-1 exit on `Y_e`: sending from `.headerReceived` encapsulates against `hdrOf K s`,
derives the epoch secret, updates `auth`, and emits chunk `0` of `ct1`. -/
theorem ySend_headerReceived (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (tape : Bytes) (htape : 32 ≤ tape.length)
    (hkem : ∀ rand : List.Vector (BitVec 8) 32, rand.toList = tape.take 32 →
      K.encaps1 (hdrOf K s) rand ≠ none) :
    let y : St F := .headerReceived { uc := { epoch := e, auth := auth, hdr := hdrOf K s },
                                      receiving_ek := freshDec 1152 }
    ∃ (y' : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F)) (c : spqrPolyApi.Chunk)
      (sec : EpochSecret),
      y.send K tape = .ok ({ msg := { epoch := e, payload := .ct1 c }, key := some sec,
                             state := .ct1Sampled y' }, tape.drop 32) ∧
      sec.epoch = e ∧ y'.uc.epoch = e ∧ y'.uc.hdr = hdrOf K s ∧ y'.receiving_ek = freshDec 1152 ∧
      y'.uc.auth = auth.update F e sec.secret ∧ y'.uc.ct1.length = 960 ∧
      EncInv y'.uc.ct1 y'.sending_ct1 := by
  intro y
  have h32 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := by
    simp only [SHARED_SECRET_SIZE, List.length_take]; omega
  obtain ⟨⟨ct1, es, ss⟩, hk⟩ := Option.ne_none_iff_exists'.1 (hkem ⟨_, h32⟩ rfl)
  have henc1 : encaps1 K (hdrOf K s) tape =
      .ok ((ct1.toList, es.toList, ss.toList), tape.drop 32) := by
    simp only [YSendHeaderReceived.encaps1_eq_match, h32, ↓reduceDIte, hk]
    rfl
  have henc := encodeBytes_spec ct1.toList (by simp) (by simp)
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec ct1.toList { idx := 0#32, s := .points (msgPoints ct1.toList) } (Or.inl rfl) (by simp)
  refine ⟨?yy, ?cc, ?sec, ?heq, ?h1, ?h2, ?h3, ?h4, ?h5, ?h6, ?h7⟩
  case heq =>
    simp only [y, States.send, Chunked.SendCt.HeaderReceived.send_ct1_chunk,
      Unchunked.SendCt.HeaderReceived.send_ct1, henc1, spqrAuthApi,
      hkdfToVec_of_le _ _ _ _ (show 32 ≤ hkdfMaxOkmLen by decide), expectEncodeBytes, spqrPolyApi,
      henc, hnext, Except.mapError, StatesResult.ofPanic, bind, Except.bind,
      liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
      Chunked.SendCt.HeaderReceived.epoch]
    rfl
  all_goals first | rfl | exact henc' | simp

/-- `Y_e` ignores messages from epochs strictly below `e`. -/
theorem yRecv_old (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (y : St F) (hy : YShape F K e auth seed? y) (m : Msg)
    (hm : m.epoch < e) :
    y.recv K m = .ok { key := none, state := y } := by
  have hle : ¬ e < m.epoch := by simp only [BitVec.lt_def] at hm ⊢; omega
  cases seed? with
  | none =>
    simp only [YShape] at hy; subst hy
    simp [States.recv, Chunked.SendCt.NoHeaderReceived.epoch, hle, hm]
  | some s =>
    rcases hy with ⟨S, dec, -, -, rfl⟩ | rfl
    · simp [States.recv, Chunked.SendCt.NoHeaderReceived.epoch, hle, hm]
    · simp [States.recv, Chunked.SendCt.HeaderReceived.epoch, hle]

/-- Receiving an honest `.hdr` chunk in `.noHeaderReceived` either accumulates the chunk
(`< 3` distinct indices) or decodes and verifies `hdrMsg`, advancing to `.headerReceived`. -/
theorem yRecv_hdr_nhr (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : AuthWf auth) (s : Seed) (S : Finset Nat) (dec : PolyDecoder)
    (hdec : DecInv (hdrMsg F K e auth s) S dec) (_hS : S.card < 3) (idx : BitVec 16) :
    let y : St F := .noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := dec }
    ∃ y' : St F, y.recv K (hdrChunkMsg F K e auth s idx) = .ok { key := none, state := y' } ∧
      YShape F K e auth (some s) y' := by
  intro y
  have hlen := hdrMsg_length F K e auth s
  have hn3 : needed 96 0 = 3 := by decide
  have hhdr : (hdrOf K s).length = 64 := by simp [hdrOf]
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (hdrMsg F K e auth s) S dec hdec (by rw [hlen]; decide) idx
  by_cases hc : (insert idx.toNat S).card < 3
  · have hnone := decodedMessage_none _ _ dec' hdec' (by rw [hlen, hn3]; exact hc)
    refine ⟨.noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := dec' }, ?_,
      Or.inl ⟨_, dec', hdec', hc, rfl⟩⟩
    simp [y, States.recv, hdrChunkMsg, Chunked.SendCt.NoHeaderReceived.epoch, hlt,
      Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk, spqrPolyApi, hadd, hnone, Except.mapError,
      StatesResult.ofPanic, bind, Except.bind]
  · have hsome := decodedMessage_spec _ _ dec' hdec' (by simp [hlen]) (by simp [hlen])
      (by rw [hlen, hn3]; omega)
    have htake : (hdrMsg F K e auth s).take 64 = hdrOf K s := List.take_left' hhdr
    have hdrop : (hdrMsg F K e auth s).drop 64 = auth.macHdrUnchecked F e (hdrOf K s) :=
      List.drop_left' hhdr
    refine ⟨.headerReceived { uc := { epoch := e, auth := auth, hdr := hdrOf K s },
                              receiving_ek := freshDec 1152 }, ?_, Or.inr rfl⟩
    simp [y, States.recv, hdrChunkMsg, Chunked.SendCt.NoHeaderReceived.epoch, hlt,
      Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk, spqrPolyApi, spqrAuthApi, hadd, hsome,
      Except.mapError, StatesResult.ofPanic, HEADER_SIZE, ENCAPSULATION_KEY_SIZE, hlen, htake,
      hdrop, decoderNew_eq 1152 (by decide), Unchunked.SendCt.NoHeaderReceived.recv_header,
      verifyHdr_macHdr F auth hauth e _ hhdr, bind, Except.bind]

/-- Once in `.headerReceived`, `Y_e` ignores all messages with `m.epoch ≤ e`. -/
theorem yRecv_headerReceived (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (m : Msg) (hm : m.epoch ≤ e) :
    let y : St F := .headerReceived { uc := { epoch := e, auth := auth, hdr := hdrOf K s },
                                      receiving_ek := freshDec 1152 }
    y.recv K m = .ok { key := none, state := y } := by
  intro y
  have hle : ¬ e < m.epoch := by simp only [BitVec.lt_def, BitVec.le_def] at hm ⊢; omega
  simp [y, States.recv, Chunked.SendCt.HeaderReceived.epoch, hle]

/-! ## Protobuf round-trip on phase-1 states -/

namespace Codec

theorem hdrOf_length (K : MlKem) (s : Seed) : (hdrOf K s).length = 64 := by
  simp [hdrOf]

theorem ekOf_length (K : MlKem) (s : Seed) : (ekOf K s).length = 1152 := by
  simp [ekOf]

theorem dkOf_length (K : MlKem) (s : Seed) : (dkOf K s).length = 2400 := by
  simp [dkOf]

theorem auth_from_into (F : ShaCompress) (auth : Authenticator) :
    (spqrAuthApi F).from_pb ((spqrAuthApi F).into_pb auth) = auth :=
  rfl

theorem encoderFromPbStateDecode_of_encInv {msg : Bytes} {enc : PolyEncoder}
    (henc : EncInv msg enc) (hmax : msg.length ≤ 2 ^ 20) (hmin : 32 ≤ msg.length) :
    encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc := by
  have h := encoder_fromPb_intoPb msg enc henc hmax hmin
  have hpb : pbToProtoPolyEncoder (protoPolyEncoderToPb enc.intoPb) = enc.intoPb := rfl
  simp [encoderFromPbStateDecode, spqrPolyApi, hpb, h,
    StatesResult.ofPanic, Except.mapError, bind, Except.bind]

theorem decoderFromPbStateDecode_of_decInv {msg : Bytes} {S : Finset Nat} {dec : PolyDecoder}
    (hdec : DecInv msg S dec) (hlen : msg.length ≤ 2 ^ 20) :
    decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec := by
  have h := decoder_fromPb_intoPb msg S dec hdec hlen
  simp [decoderFromPbStateDecode, spqrPolyApi, pbToProtoPolyDecoder, protoPolyDecoderToPb, h,
    StatesResult.ofPanic, Except.mapError, bind, Except.bind]

theorem noHeaderReceived_codec (F : ShaCompress) (e : Epoch) (auth : Authenticator)
    {msg : Bytes} {S : Finset Nat} {dec : PolyDecoder}
    (hdec : DecInv msg S dec) (hmsg : msg.length = 96) :
    let y : St F := .noHeaderReceived { uc := { epoch := e, auth := auth }, receiving_hdr := dec }
    States.from_pb spqrPolyApi (spqrAuthApi F) y.into_pb = .ok y := by
  intro y
  have hpts : dec.ptsNeeded = 48 := by
    rw [hdec.ptsNeeded, hmsg]
  have hdecPb :
      decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec :=
    decoderFromPbStateDecode_of_decInv hdec (by omega)
  have hptsPb : (spqrPolyApi.decoder_into_pb dec).ptsNeeded = 48#32 := by
    simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpts]
  simp only [y, States.into_pb, States.from_pb,
    Chunked.SendCt.NoHeaderReceived.into_pb, Chunked.SendCt.NoHeaderReceived.from_pb,
    Unchunked.SendCt.NoHeaderReceived.into_pb, Unchunked.SendCt.NoHeaderReceived.from_pb,
    hptsPb, hdecPb, auth_from_into, bind, Except.bind]
  rfl

theorem freshDec_decInv (len : Nat) (heven : len % 2 = 0) :
    DecInv (List.replicate len 0#8) ∅ (freshDec len) := by
  have h := decInv_freshDec (List.replicate len 0#8) (by rw [List.length_replicate]; exact heven)
  rwa [List.length_replicate] at h

end Codec

/-- Phase-1 EK-side states round-trip through `States.from_pb ∘ States.into_pb`. -/
theorem xShape_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x : St F) (hx : XShape F K e auth seed? x) :
    States.from_pb spqrPolyApi (spqrAuthApi F) x.into_pb = .ok x := by
  cases seed? with
  | none =>
    subst hx
    rfl
  | some s =>
    obtain ⟨enc, henc, rfl⟩ := hx
    have hlen : (hdrMsg F K e auth s).length = 96 := hdrMsg_length F K e auth s
    have hencPb :
        encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
      Codec.encoderFromPbStateDecode_of_encInv henc (by omega) (by omega)
    simp [States.into_pb, States.from_pb,
      Chunked.SendEk.KeysSampled.into_pb, Chunked.SendEk.KeysSampled.from_pb,
      Unchunked.SendEk.HeaderSent.into_pb, Unchunked.SendEk.HeaderSent.from_pb,
      DECAPSULATION_KEY_SIZE, ENCAPSULATION_KEY_SIZE,
      Codec.dkOf_length, Codec.ekOf_length, hencPb, Codec.auth_from_into,
      bind, Except.bind]

/-- Phase-1 CT-side states round-trip through `States.from_pb ∘ States.into_pb`. -/
theorem yShape_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (y : St F) (hy : YShape F K e auth seed? y) :
    States.from_pb spqrPolyApi (spqrAuthApi F) y.into_pb = .ok y := by
  cases seed? with
  | none =>
    subst hy
    exact Codec.noHeaderReceived_codec F e auth (Codec.freshDec_decInv 96 (by decide))
      (List.length_replicate)
  | some s =>
    rcases hy with ⟨S, dec, hdec, -, rfl⟩ | rfl
    · exact Codec.noHeaderReceived_codec F e auth hdec (hdrMsg_length F K e auth s)
    · have hdecPb :
          decoderFromPbStateDecode spqrPolyApi
            (some (spqrPolyApi.decoder_into_pb (freshDec 1152))) = .ok (freshDec 1152) :=
        Codec.decoderFromPbStateDecode_of_decInv (Codec.freshDec_decInv 1152 (by decide))
          (by rw [List.length_replicate]; decide)
      have hptsPb :
          (spqrPolyApi.decoder_into_pb (freshDec 1152)).ptsNeeded.toNat = 576 := by
        decide
      simp [States.into_pb, States.from_pb,
        Chunked.SendCt.HeaderReceived.into_pb, Chunked.SendCt.HeaderReceived.from_pb,
        Unchunked.SendCt.HeaderReceived.into_pb, Unchunked.SendCt.HeaderReceived.from_pb,
        HEADER_SIZE, ENCAPSULATION_KEY_SIZE, Codec.hdrOf_length, hptsPb, hdecPb,
        Codec.auth_from_into, bind, Except.bind]

/-! ## Phase-1 assembly -/

theorem yRecv_hdr (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : AuthWf auth) (s : Seed) (y : St F) (hy : YShape F K e auth (some s) y)
    (idx : BitVec 16) :
    ∃ y' : St F, y.recv K (hdrChunkMsg F K e auth s idx) = .ok { key := none, state := y' } ∧
      YShape F K e auth (some s) y' := by
  rcases hy with ⟨S, dec, hdec, hS, rfl⟩ | rfl
  · exact yRecv_hdr_nhr F K e auth hauth s S dec hdec hS idx
  · exact ⟨_, yRecv_headerReceived F K e auth s _ (BitVec.le_refl e), Or.inr rfl⟩

theorem yRecv (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : AuthWf auth) (seed? : Option Seed) (y : St F) (hy : YShape F K e auth seed? y)
    (m : Msg) (hm : ToYOk F K e auth seed? m) :
    ∃ y' : St F, y.recv K m = .ok { key := none, state := y' } ∧ YShape F K e auth seed? y' := by
  rcases hm with hlt | ⟨s, rfl, idx, rfl⟩
  · exact ⟨y, yRecv_old F K e auth seed? y hy m hlt, hy⟩
  · exact yRecv_hdr F K e auth hauth s y hy idx

theorem xSend (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (hauth : AuthWf auth) (seed? : Option Seed) (x : St F) (hx : XShape F K e auth seed? x)
    (tape : Bytes) (htape : 64 ≤ tape.length) :
    ∃ (s : Seed) (m : Msg) (x' : St F) (tape' : Bytes),
      (seed? = none ∨ seed? = some s) ∧
      x.send K tape = .ok ({ msg := m, key := none, state := x' }, tape') ∧
      XShape F K e auth (some s) x' ∧ ToYOk F K e auth (some s) m := by
  cases seed? with
  | none =>
    obtain ⟨s, -, x', h, hx'⟩ := xSend_unsampled F K e auth hauth x hx tape htape
    exact ⟨s, _, x', _, Or.inl rfl, h, hx', Or.inr ⟨s, rfl, 0#16, rfl⟩⟩
  | some s =>
    obtain ⟨idx, x', h, hx'⟩ := xSend_sampled F K e auth s x hx tape
    exact ⟨s, _, x', _, Or.inr rfl, h, hx', Or.inr ⟨s, rfl, idx, rfl⟩⟩

theorem yShape_some_of_none (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (y : St F) (hy : YShape F K e auth none y) (s : Seed) : YShape F K e auth (some s) y := by
  simp only [YShape] at hy ⊢
  subst hy
  refine Or.inl ⟨∅, freshDec 96, ?_, by simp, rfl⟩
  have h := decInv_freshDec (hdrMsg F K e auth s) (by rw [hdrMsg_length])
  rwa [hdrMsg_length] at h

theorem toYOk_some_of_none (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (m : Msg) (hm : ToYOk F K e auth none m) (s : Seed) : ToYOk F K e auth (some s) m := by
  rcases hm with h | ⟨_, h, -⟩
  · exact Or.inl h
  · cases h

/-- `States.init_a` and `States.init_b` with the same `authKey` satisfy `InSync1` at epoch `1`. -/
theorem inSync1_init (F : ShaCompress) (K : MlKem) (authKey : Bytes) :
    ∃ x y : St F, States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok x ∧
      States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok y ∧
      InSync1 F K 1#64 (Authenticator.new F authKey 1#64) none x y [] [] := by
  have hdec : ∀ n, n = 96 → spqrPolyApi.decoder_new n = .ok (.ok (freshDec 96)) := by
    rintro n rfl
    simp only [spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError]
  refine ⟨_, _, rfl, ?_, authWf_new F authKey 1#64, rfl, rfl, by simp, by simp⟩
  simp only [States.init_b, Chunked.SendCt.NoHeaderReceived.new]
  rw [hdec]
  all_goals rfl

/-- EK-side send preserves `InSync1` on any coin tape of length `≥ 64`. -/
theorem inSync1_sendX (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg)
    (h : InSync1 F K e auth seed? x y toY toX) (tape : Bytes) (htape : 64 ≤ tape.length) :
    ∃ (s : Seed) (m : Msg) (x' : St F) (tape' : Bytes),
      x.send K tape = .ok ({ msg := m, key := none, state := x' }, tape') ∧
      InSync1 F K e auth (some s) x' y (toY ++ [m]) toX := by
  obtain ⟨s, m, x', tape', hs, hsend, hx', hm⟩ := xSend F K e auth h.hauth seed? x h.hx tape htape
  refine ⟨s, m, x', tape', hsend, h.hauth, hx', ?_, ?_, h.htoX⟩
  · rcases hs with rfl | rfl
    · exact yShape_some_of_none F K e auth y h.hy s
    · exact h.hy
  · intro m' hm'
    rcases List.mem_append.1 hm' with hm' | hm'
    · rcases hs with rfl | rfl
      · exact toYOk_some_of_none F K e auth m' (h.htoY m' hm') s
      · exact h.htoY m' hm'
    · rw [List.mem_singleton] at hm'
      subst hm'
      exact hm

/-- CT-side send prior to `.headerReceived` emits `.none` and preserves `InSync1`. -/
theorem inSync1_sendY (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg)
    (h : InSync1 F K e auth seed? x y toY toX) (hnhr : ∀ s, y ≠ .headerReceived s)
    (tape : Bytes) :
    y.send K tape =
        .ok ({ msg := { epoch := e, payload := .none }, key := none, state := y }, tape) ∧
      InSync1 F K e auth seed? x y toY (toX ++ [{ epoch := e, payload := .none }]) := by
  refine ⟨ySend_noHeader F K e auth seed? y h.hy hnhr tape, h.hauth, h.hx, h.hy, h.htoY, ?_⟩
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · exact h.htoX m hm
  · rw [List.mem_singleton] at hm
    exact Or.inr hm

/-- EK-side receive of any `m ∈ toX` is a no-op and preserves `InSync1`. -/
theorem inSync1_recvX (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg)
    (h : InSync1 F K e auth seed? x y toY toX) (m : Msg) (hm : m ∈ toX) :
    x.recv K m = .ok { key := none, state := x } :=
  xRecv F K e auth seed? x h.hx m (h.htoX m hm)

/-- CT-side receive of any `m ∈ toY` succeeds without key output and preserves `InSync1`. -/
theorem inSync1_recvY (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg)
    (h : InSync1 F K e auth seed? x y toY toX) (m : Msg) (hm : m ∈ toY) :
    ∃ y' : St F, y.recv K m = .ok { key := none, state := y' } ∧
      InSync1 F K e auth seed? x y' toY toX := by
  obtain ⟨y', hr, hy'⟩ := yRecv F K e auth h.hauth seed? y h.hy m (h.htoY m hm)
  exact ⟨y', hr, { h with hy := hy' }⟩

/-- Both parties' phase-1 states round-trip through `States.from_pb ∘ States.into_pb`. -/
theorem inSync1_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x y : St F) (toY toX : List Msg)
    (h : InSync1 F K e auth seed? x y toY toX) :
    States.from_pb spqrPolyApi (spqrAuthApi F) x.into_pb = .ok x ∧
      States.from_pb spqrPolyApi (spqrAuthApi F) y.into_pb = .ok y :=
  ⟨xShape_codec F K e auth seed? x h.hx, yShape_codec F K e auth seed? y h.hy⟩

end CryptoVerification.SpqrV1Sync.InSync
