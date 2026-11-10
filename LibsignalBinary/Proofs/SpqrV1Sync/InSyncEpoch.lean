/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
import LibsignalBinary.Proofs.SpqrV1Sync.ErasureCode

/-!
# Full-Epoch Braid Synchronization Invariant (`InSyncE` and `InSync`)

Extends the phase-1 invariant (`InSyncCalib`) across a complete SPQR V1 braid epoch and across the
inter-epoch role swap on `States spqrPolyApi (spqrAuthApi F)`:
* At epoch `e` (`e.toNat + 1 < 2 ^ 64`), `ekSide e` designates the EK side `X_e` (`Party.a` at odd
  epochs) and the CT side `Y_e`. The ghost coin transcript `c : Coins` progresses monotonically
  through `.init`, `.seed s`, and `.both s r`.
* `XShapeE` and `YShapeE` describe the reachable per-party states (including `XLag`, where `X_e` has
  completed `recv_ct2` and advanced to `.noHeaderReceived` at `e + 1`), coupled by causality
  invariants `hcausal` and `hlag` and monotone in-flight predicates `ToYOkE` and `ToXOkE`.
* Under `KemOk K s r` (derived from `K.honestExchangeFails s r = false`), both parties derive the
  same epoch secret `secOf F K e s r` and updated authenticator `authNext F K e auth s r`, and
  receiving `.none` at `e + 1` swaps EK/CT roles for epoch `e + 1` (`inSyncE_next`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Braid

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.InSync
open CryptoGames.LibsignalSession (ShaCompress)

/-! ## Per-epoch ghost values -/

/-- 32-byte encapsulation randomness drawn by `Y_e` when sending from `.headerReceived`. -/
abbrev EncRand := List.Vector (BitVec 8) 32

/-- Ghost coins drawn so far in epoch `e`: none, `X_e`'s seed `s`, or both `s` and `Y_e`'s `r`. -/
inductive Coins where
  | init
  | seed (s : Seed)
  | both (s : Seed) (r : EncRand)

def Coins.seed? : Coins → Option Seed
  | .init => none
  | .seed s => some s
  | .both s _ => some s

/-- Raw `K.encaps1` result on `hdrOf K s` and `r`. -/
def encOf (K : MlKem) (s : Seed) (r : EncRand) :
    Option (List.Vector (BitVec 8) 960 × List.Vector (BitVec 8) 2080 × List.Vector (BitVec 8) 32) :=
  K.encaps1 (hdrOf K s) r

/-- First ciphertext `ct1` (960 bytes when `encaps1` succeeds). -/
def ct1Of (K : MlKem) (s : Seed) (r : EncRand) : Bytes :=
  ((encOf K s r).map fun t => t.1.toList).getD []

/-- Encapsulation state `es` (2080 bytes when `encaps1` succeeds). -/
def esOf (K : MlKem) (s : Seed) (r : EncRand) : Bytes :=
  ((encOf K s r).map fun t => t.2.1.toList).getD []

/-- Raw 32-byte ML-KEM shared secret output by `encaps1`. -/
def ss0Of (K : MlKem) (s : Seed) (r : EncRand) : Bytes :=
  ((encOf K s r).map fun t => t.2.2.toList).getD []

/-- Second ciphertext `ct2` produced by `encaps2` on `ekOf K s` and `esOf K s r`. -/
def ct2Of (K : MlKem) (s : Seed) (r : EncRand) : Bytes :=
  match encaps2 K (ekOf K s) (esOf K s r) with
  | .ok ct2 => ct2
  | .error _ => []

/-- 8-byte big-endian encoding of a 64-bit integer. -/
def be64 (v : BitVec 64) : Bytes :=
  [ v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
    v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb'  8 8, v.extractLsb'  0 8 ]

/-- 32-byte HKDF epoch secret derived from `ss0Of K s r` at epoch `e`. -/
def secOf (F : ShaCompress) (K : MlKem) (e : Epoch) (s : Seed) (r : EncRand) : Bytes :=
  hkdfToVecUnchecked F (List.replicate 32 0#8) (ss0Of K s r) (sckaKeyInfoPrefix ++ be64 e) 32

/-- Updated authenticator `auth.update F e (secOf F K e s r)` after epoch `e`. -/
def authNext (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) : Authenticator :=
  auth.update F e (secOf F K e s r)

/-- 160-byte authenticated `ct2` payload `ct2Of K s r ++ auth'.macCtUnchecked F e (ct1 ‖ ct2)`. -/
def c2Msg (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) : Bytes :=
  ct2Of K s r ++ (authNext F K e auth s r).macCtUnchecked F e (ct1Of K s r ++ ct2Of K s r)

/-- Honest chunk `idx` of `msg` at epoch `e` wrapped in payload constructor `pl`. -/
noncomputable def chunkMsg (pl : spqrPolyApi.Chunk → MessagePayload spqrPolyApi) (e : Epoch)
    (msg : Bytes) (idx : BitVec 16) : Msg where
  epoch := e
  payload := pl (spqrPolyApi.mkChunk idx (Erasure.chunkData msg idx))

def noneMsg (e : Epoch) : Msg := { epoch := e, payload := .none }

/-- `Ct1Ack true` message at epoch `e`. -/
def ackMsg (e : Epoch) : Msg := { epoch := e, payload := .ct1Ack true }

/-! ## ML-KEM exchange correctness condition -/

/-- `encaps2` succeeds on `(ekOf K s, esOf K s r)` and `decaps` recovers `ss0Of K s r`. -/
def DecapsRecovers (K : MlKem) (s : Seed) (r : EncRand) : Prop :=
  ∃ ct2, encaps2 K (ekOf K s) (esOf K s r) = .ok ct2 ∧
    decaps K (dkOf K s) (ct1Of K s r) ct2 = .ok (ss0Of K s r)

/-- Per-epoch ML-KEM correctness predicates for keygen seed `s` and encapsulation randomness `r`. -/
structure KemOk (K : MlKem) (s : Seed) (r : EncRand) : Prop where
  /-- `encaps1` succeeds on `(hdrOf K s, r)`. -/
  encaps1_ok : encOf K s r ≠ none
  /-- `ekOf K s` passes `ek_matches_header` against `hdrOf K s`. -/
  ek_matches : ek_matches_header K (ekOf K s) (hdrOf K s) = true
  /-- `encaps2` succeeds and `decaps` recovers `ss0Of K s r`. -/
  decaps_ok : DecapsRecovers K s r

/-! ## Auxiliary ML-KEM and MAC lemmas -/

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

theorem generate_seed (K : MlKem) (s : Seed) :
    generate K s.toList =
      .ok ({ ek := ekOf K s, dk := dkOf K s, hdr := hdrOf K s }, []) := by
  have h64 : (s.toList.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE := by
    simp [KEY_GENERATION_SEED_SIZE]
  have hs : (⟨s.toList.take KEY_GENERATION_SEED_SIZE, h64⟩ : Seed) = s := by
    apply Subtype.ext; exact List.take_of_length_le (le_of_eq s.2)
  rw [generate_eq_match, dite_eq_left h64, hs]
  simp [ekOf, dkOf, hdrOf, KEY_GENERATION_SEED_SIZE]

theorem encaps1_rand (K : MlKem) (hdr : Header) (r : EncRand) :
    encaps1 K hdr r.toList =
      match K.encaps1 hdr r with
      | none => .error .encaps1Failed
      | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), []) := by
  have h32 : (r.toList.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := by
    simp [SHARED_SECRET_SIZE]
  have hr : (⟨r.toList.take SHARED_SECRET_SIZE, h32⟩ : EncRand) = r := by
    apply Subtype.ext; exact List.take_of_length_le (le_of_eq r.2)
  have hd : r.toList.drop SHARED_SECRET_SIZE = [] := List.drop_eq_nil_of_le (le_of_eq r.2)
  rw [encaps1_eq_match, dite_eq_left h32, hr, hd]

/-- `K.honestExchangeFails s r = false` implies `KemOk K s r`. -/
theorem kemOk_of_honestFail (K : MlKem) (s : Seed) (r : EncRand)
    (h : K.honestExchangeFails s r = false) : KemOk K s r := by
  unfold MlKem.honestExchangeFails at h
  rw [generate_seed] at h
  simp only at h
  rw [encaps1_rand] at h
  rcases henc : K.encaps1 (hdrOf K s) r with _ | ⟨ct1, es, ss⟩
  · rw [henc] at h; simp at h
  · rw [henc] at h
    simp only at h
    have hek : ek_matches_header K (ekOf K s) (hdrOf K s) = true := by
      by_contra hne; simp [hne] at h
    simp only [hek, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    have hencOf : encOf K s r = some (ct1, es, ss) := henc
    refine ⟨by simp [hencOf], hek, ?_⟩
    have hes : esOf K s r = es.toList := by simp [esOf, hencOf]
    have hct1 : ct1Of K s r = ct1.toList := by simp [ct1Of, hencOf]
    have hss : ss0Of K s r = ss.toList := by simp [ss0Of, hencOf]
    rcases h2 : encaps2 K (ekOf K s) es.toList with _ | ct2
    · rw [h2] at h; simp at h
    · rw [h2] at h
      simp only at h
      rcases h3 : decaps K (dkOf K s) ct1.toList ct2 with _ | ssA
      · rw [h3] at h; simp at h
      · rw [h3] at h
        simp only [decide_eq_false_iff_not, not_not] at h
        exact ⟨ct2, by rw [hes, h2], by rw [hct1, hss, h3, h]⟩

theorem ekOf_length (K : MlKem) (s : Seed) : (ekOf K s).length = 1152 := by simp [ekOf]

theorem ct1Of_length (K : MlKem) (s : Seed) (r : EncRand) (hk : KemOk K s r) :
    (ct1Of K s r).length = 960 := by
  rcases h : encOf K s r with _ | ⟨ct1, es, ss⟩
  · exact absurd h hk.encaps1_ok
  · simp [ct1Of, h]

theorem ct1Of_length_le (K : MlKem) (s : Seed) (r : EncRand) : (ct1Of K s r).length ≤ 960 := by
  rcases h : encOf K s r with _ | ⟨ct1, es, ss⟩ <;> simp [ct1Of, h]

theorem esOf_length (K : MlKem) (s : Seed) (r : EncRand) (hk : KemOk K s r) :
    (esOf K s r).length = 2080 := by
  rcases h : encOf K s r with _ | ⟨ct1, es, ss⟩
  · exact absurd h hk.encaps1_ok
  · simp [esOf, h]

theorem encaps2_eq (K : MlKem) (s : Seed) (r : EncRand) (hk : KemOk K s r) :
    encaps2 K (ekOf K s) (esOf K s r) = .ok (ct2Of K s r) := by
  obtain ⟨ct2, h2, -⟩ := hk.decaps_ok
  simp [ct2Of, h2]

theorem encaps2_ok_length {K : MlKem} {ek : EncapsulationKey} {es : EncapsulationState}
    {ct2 : Ciphertext2} (h : encaps2 K ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  cases hf : potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es with
  | error e => simp [hf] at h; cases h
  | ok fx =>
    simp only [hf, bind, Except.bind] at h
    split at h
    · cases h; simp
    · cases h

theorem ct2Of_length (K : MlKem) (s : Seed) (r : EncRand) (hk : KemOk K s r) :
    (ct2Of K s r).length = 128 :=
  encaps2_ok_length (encaps2_eq K s r hk)

theorem c2Msg_length (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) : (c2Msg F K e auth s r).length = 160 := by
  simp [c2Msg, ct2Of_length K s r hk]

theorem authWf_update (F : ShaCompress) (auth : Authenticator) (ep : Epoch) (k : Bytes) :
    AuthWf (auth.update F ep k) := by
  simp [AuthWf, Authenticator.update, hkdfToVecUnchecked, hkdfToSliceUnchecked]

/-- `Authenticator.macCt` succeeds without panicking on a well-formed authenticator when
`ct.length ≤ 2 ^ 20`. -/
theorem macCt_eq (F : ShaCompress) (a : Authenticator) (ha : AuthWf a) (e : Epoch) (ct : Bytes)
    (hct : ct.length ≤ 2 ^ 20) : a.macCt F e ct = .ok (a.macCtUnchecked F e ct) := by
  have hlab : Authenticator.ctLabel.length = 35 := by decide
  have hbe : (CryptoGames.HMAC.toBEBytes 8 e).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
  apply Authenticator.macCt_of_lt
  · rw [ha]; decide
  · simp only [List.length_append, hlab, hbe]; omega

/-- `Authenticator.verifyCtError` accepts the tag computed by `macCtUnchecked`. -/
theorem verifyCt_macCt (F : ShaCompress) (a : Authenticator) (ha : AuthWf a) (e : Epoch)
    (ct : Bytes) (hct : ct.length ≤ 2 ^ 20) :
    a.verifyCtError F e ct (a.macCtUnchecked F e ct) = .ok (.ok ()) := by
  have hlab : Authenticator.ctLabel.length = 35 := by decide
  have hbe : (CryptoGames.HMAC.toBEBytes 8 e).length = 8 := by simp [CryptoGames.HMAC.toBEBytes]
  have hself : ∀ (l : Bytes) (r : BitVec 8),
      (l.zip l).foldl (fun r (a, b) => r ||| (a ^^^ b)) r = r := by
    intro l; induction l with
    | nil => intro r; rfl
    | cons a l ih => intro r; simp [ih]
  unfold Authenticator.verifyCtError
  rw [Authenticator.verifyCt_eq_ok_prefix F a e ct _ (by rw [ha]; decide)
    (by simp only [List.length_append, hlab, hbe]; omega) (by simp)]
  simp [Authenticator.verifyCt_prefix, compare_prefix, hself, isNonZero, inz, Except.map,
    Except.mapError]

/-! ## Per-party state shapes at epoch `e` -/

/-- `X_e` in `.headerSent`: sending `ek` chunks and decoding `ct1`. -/
def XHS (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) : Prop :=
  ∃ (enc : PolyEncoder) (S : Finset Nat) (dec : PolyDecoder),
    EncInv (ekOf K s) enc ∧ DecInv (ct1Of K s r) S dec ∧ S.card < 30 ∧
    x = .headerSent { uc := { epoch := e, auth := auth, dk := dkOf K s },
                      sending_ek := enc, receiving_ct1 := dec }

/-- `X_e` in `.ct1Received`: `ct1` decoded, sending `ek` chunks as `.ekCt1Ack`. -/
def XC1R (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) : Prop :=
  ∃ enc : PolyEncoder, EncInv (ekOf K s) enc ∧
    x = .ct1Received { uc := { epoch := e, auth := auth, dk := dkOf K s, ct1 := ct1Of K s r },
                       sending_ek := enc }

/-- `X_e` in `.ekSentCt1Received`: decoding the 160-byte `c2Msg` (`5 = needed 160 0`). -/
def XESCR (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) : Prop :=
  ∃ (S : Finset Nat) (dec : PolyDecoder), DecInv (c2Msg F K e auth s r) S dec ∧ S.card < 5 ∧
    x = .ekSentCt1Received { uc := { epoch := e, auth := auth, dk := dkOf K s,
                                     ct1 := ct1Of K s r },
                             receiving_ct2 := dec }

/-- `X_e` already advanced to `.noHeaderReceived` at `e + 1` with `authNext`. -/
def XLag (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) : Prop :=
  x = .noHeaderReceived { uc := { epoch := e + 1#64, auth := authNext F K e auth s r },
                          receiving_hdr := freshDec 96 }

/-- Reachable EK-side state shape indexed by `Coins`. -/
def XShapeE (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) :
    Coins → St F → Prop
  | .init, x => XShape F K e auth none x
  | .seed s, x => XShape F K e auth (some s) x
  | .both s r, x => XShape F K e auth (some s) x ∨ XHS F K e auth s r x ∨
      XC1R F K e auth s r x ∨ XESCR F K e auth s r x ∨ XLag F K e auth s r x

/-- `Y_e` in `.ct1Sampled`: sending `ct1` and decoding `ek` (`36 = needed 1152 0`). -/
def YC1S (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) : Prop :=
  ∃ (enc : PolyEncoder) (S : Finset Nat) (dec : PolyDecoder),
    EncInv (ct1Of K s r) enc ∧ DecInv (ekOf K s) S dec ∧ S.card < 36 ∧
    y = .ct1Sampled { uc := { epoch := e, auth := authNext F K e auth s r, hdr := hdrOf K s,
                              es := esOf K s r, ct1 := ct1Of K s r },
                      sending_ct1 := enc, receiving_ek := dec }

/-- `Y_e` in `.ekReceivedCt1Sampled`: `ek` decoded, `ct1` unacknowledged. -/
def YEkR (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) : Prop :=
  ∃ enc : PolyEncoder, EncInv (ct1Of K s r) enc ∧
    y = .ekReceivedCt1Sampled { uc := { epoch := e, auth := authNext F K e auth s r,
                                        es := esOf K s r, ek := ekOf K s, ct1 := ct1Of K s r },
                                sending_ct1 := enc }

/-- `Y_e` in `.ct1Acknowledged`: `ct1` acknowledged, decoding `ek`. -/
def YC1A (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) : Prop :=
  ∃ (S : Finset Nat) (dec : PolyDecoder), DecInv (ekOf K s) S dec ∧ S.card < 36 ∧
    y = .ct1Acknowledged { uc := { epoch := e, auth := authNext F K e auth s r,
                                   hdr := hdrOf K s, es := esOf K s r, ct1 := ct1Of K s r },
                           receiving_ek := dec }

/-- `Y_e` in `.ct2Sampled`: sending `c2Msg` chunks until an epoch-`(e + 1)` message arrives. -/
def YC2S (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) : Prop :=
  ∃ enc : PolyEncoder, EncInv (c2Msg F K e auth s r) enc ∧
    y = .ct2Sampled { uc := { epoch := e, auth := authNext F K e auth s r },
                      sending_ct2 := enc }

/-- Reachable CT-side state shape indexed by `Coins`. -/
def YShapeE (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) :
    Coins → St F → Prop
  | .init, y => YShape F K e auth none y
  | .seed s, y => YShape F K e auth (some s) y
  | .both s r, y => YC1S F K e auth s r y ∨ YEkR F K e auth s r y ∨ YC1A F K e auth s r y ∨
      YC2S F K e auth s r y

/-! ## In-flight message predicates -/

/-- Honest messages in flight toward `Y_e` under ghost coins `c`. -/
def ToYOkE (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (m : Msg) : Prop :=
  m.epoch < e ∨
  (∃ s, c.seed? = some s ∧ ∃ idx, m = hdrChunkMsg F K e auth s idx) ∨
  (∃ s r, c = .both s r ∧
    ((∃ idx, m = chunkMsg .ek e (ekOf K s) idx) ∨
     (∃ idx, m = chunkMsg .ekCt1Ack e (ekOf K s) idx) ∨ m = ackMsg e)) ∨
  m = noneMsg (e + 1#64)

/-- Honest messages in flight toward `X_e` under ghost coins `c`. -/
def ToXOkE (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (m : Msg) : Prop :=
  m.epoch < e ∨ m = noneMsg e ∨
  ∃ s r, c = .both s r ∧
    ((∃ idx, m = chunkMsg .ct1 e (ct1Of K s r) idx) ∨
     (∃ idx, m = chunkMsg .ct2 e (c2Msg F K e auth s r) idx))

/-! ## Full-epoch synchronization invariant -/

/-- Full-epoch synchronization invariant at epoch `e` with `X` on the EK side and `Y` on the
CT side. -/
structure InSyncE (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (x y : St F) (toY toX : List Msg) : Prop where
  /-- Epoch non-overflow bound (`recv_ct2` and `recv_next_epoch` guard `e ≠ allOnes`). -/
  hepoch : e.toNat + 1 < 2 ^ 64
  hauth : AuthWf auth
  hx : XShapeE F K e auth c x
  hy : YShapeE F K e auth c y
  /-- Drawn coins satisfy `KemOk`. -/
  hkem : ∀ s r, c = .both s r → KemOk K s r
  /-- Causality: `X` reaches `XESCR`/`XLag` or sees a `.ct2` chunk only after `Y` reaches `YC2S`. -/
  hcausal : ∀ s r, c = .both s r →
    (XESCR F K e auth s r x ∨ XLag F K e auth s r x ∨
      ∃ idx, chunkMsg .ct2 e (c2Msg F K e auth s r) idx ∈ toX) →
    YC2S F K e auth s r y
  /-- `noneMsg (e + 1)` is in flight toward `Y` only after `X` reaches `XLag`. -/
  hlag : noneMsg (e + 1#64) ∈ toY → ∃ s r, c = .both s r ∧ XLag F K e auth s r x
  htoY : ∀ m ∈ toY, ToYOkE F K e auth c m
  htoX : ∀ m ∈ toX, ToXOkE F K e auth c m

/-- Identifier for the two protocol parties. -/
inductive Party where
  | a
  | b
  deriving DecidableEq

/-- Designates the EK side at epoch `e` (`Party.a` at odd epochs, `Party.b` at even epochs). -/
def ekSide (e : Epoch) : Party := if e.toNat % 2 = 1 then .a else .b

/-- Two-party synchronization invariant orienting `(stA, stB)` into `(X, Y)` via `ekSide e`. -/
def InSync (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (c : Coins)
    (stA stB : St F) (toA toB : List Msg) : Prop :=
  match ekSide e with
  | .a => InSyncE F K e auth c stA stB toB toA
  | .b => InSyncE F K e auth c stB stA toA toB

/-! ## EK-side (`X_e`) send transitions -/

/-- `.headerSent` emits the next `.ek` chunk and preserves `XHS`. -/
theorem xSend_hs (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) (hx : XHS F K e auth s r x) (tape : Bytes) :
    ∃ (idx : BitVec 16) (x' : St F),
      x.send K tape = .ok ({ msg := chunkMsg .ek e (ekOf K s) idx, key := none, state := x' },
        tape) ∧ XHS F K e auth s r x' := by
  obtain ⟨enc, S, dec, henc, hdec, hS, rfl⟩ := hx
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (ekOf K s) enc henc (by rw [ekOf_length]; decide)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', S, dec, henc', hdec, hS, rfl⟩
  simp only [States.send, Chunked.SendEk.HeaderSent.send_ek_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic, Chunked.SendEk.HeaderSent.epoch]
  rfl

/-- `.ct1Received` emits the next `.ekCt1Ack` chunk and preserves `XC1R`. -/
theorem xSend_c1r (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) (hx : XC1R F K e auth s r x) (tape : Bytes) :
    ∃ (idx : BitVec 16) (x' : St F),
      x.send K tape =
        .ok ({ msg := chunkMsg .ekCt1Ack e (ekOf K s) idx, key := none, state := x' }, tape) ∧
      XC1R F K e auth s r x' := by
  obtain ⟨enc, henc, rfl⟩ := hx
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (ekOf K s) enc henc (by rw [ekOf_length]; decide)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', henc', rfl⟩
  simp only [States.send, Chunked.SendEk.Ct1Received.send_ek_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic, Chunked.SendEk.Ct1Received.epoch]
  rfl

/-- `.ekSentCt1Received` emits `ackMsg e` and leaves the state unchanged. -/
theorem xSend_escr (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) (hx : XESCR F K e auth s r x) (tape : Bytes) :
    x.send K tape = .ok ({ msg := ackMsg e, key := none, state := x }, tape) := by
  obtain ⟨S, dec, -, -, rfl⟩ := hx
  rfl

/-- `XLag` emits `noneMsg (e + 1)` and leaves the state unchanged. -/
theorem xSend_lag (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (x : St F) (hx : XLag F K e auth s r x) (tape : Bytes) :
    x.send K tape = .ok ({ msg := noneMsg (e + 1#64), key := none, state := x }, tape) := by
  subst hx
  rfl

/-! ## EK-side (`X_e`) receive transitions -/

/-- `.keysSampled` receiving its first `.ct1` chunk initializes the 960-byte `ct1` decoder and
`ek` encoder, transitioning to `XHS`. -/
theorem xRecv_ks_ct1 (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) (x : St F) (hx : XShape F K e auth (some s) x)
    (idx : BitVec 16) :
    ∃ x' : St F, x.recv K (chunkMsg .ct1 e (ct1Of K s r) idx) = .ok { key := none, state := x' } ∧
      XHS F K e auth s r x' := by
  obtain ⟨enc_hdr, -, rfl⟩ := hx
  have hct1 : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
  have hek : (ekOf K s).length = 1152 := by simp [ekOf]
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  have hdec0 : DecInv (ct1Of K s r) ∅ (freshDec 960) := by
    have h := decInv_freshDec (ct1Of K s r) (by rw [hct1])
    rwa [hct1] at h
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (ct1Of K s r) ∅ (freshDec 960) hdec0 (by rw [hct1]; decide) idx
  have henc_ek := encodeBytes_spec (ekOf K s) (by simp [hek]) (by simp [hek])
  let enc_ek : PolyEncoder := { idx := 0#32, s := .points (msgPoints (ekOf K s)) }
  refine ⟨.headerSent { uc := { epoch := e, auth := auth, dk := dkOf K s },
                        sending_ek := enc_ek, receiving_ct1 := dec' },
    ?_, ⟨enc_ek, insert idx.toNat ∅, dec', Or.inl rfl, hdec', by simp, rfl⟩⟩
  simp [States.recv, chunkMsg, Chunked.SendEk.KeysSampled.epoch, hlt,
    Chunked.SendEk.KeysSampled.recv_ct1_chunk, CIPHERTEXT1_SIZE, expectDecoderNew, spqrPolyApi,
    decoderNew_eq 960 (by decide), hadd, Unchunked.SendEk.HeaderSent.send_ek, expectEncodeBytes,
    henc_ek, enc_ek, StatesResult.ofPanic, Except.mapError, bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

/-- `.keysSampled` ignores messages of epoch `< e` and non-`.ct1` messages at epoch `e`. -/
theorem xRecv_ks_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (x : St F) (hx : XShape F K e auth (some s) x) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ ∀ c, m.payload ≠ .ct1 c)) :
    x.recv K m = .ok { key := none, state := x } := by
  obtain ⟨enc, -, rfl⟩ := hx
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendEk.KeysSampled.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendEk.KeysSampled.epoch]

/-- `.headerSent` receiving an honest `.ct1` chunk either stays in `XHS` or finishes decoding
`ct1` and transitions to `XC1R`. -/
theorem xRecv_hs_ct1 (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) (x : St F) (hx : XHS F K e auth s r x) (idx : BitVec 16) :
    ∃ x' : St F, x.recv K (chunkMsg .ct1 e (ct1Of K s r) idx) = .ok { key := none, state := x' } ∧
      (XHS F K e auth s r x' ∨ XC1R F K e auth s r x') := by
  obtain ⟨enc, S, dec, henc, hdec, _hS, rfl⟩ := hx
  have hlen := ct1Of_length K s r hk
  have hn30 : needed 960 0 = 30 := by decide
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (ct1Of K s r) S dec hdec (by rw [hlen]; decide) idx
  by_cases hc : (insert idx.toNat S).card < 30
  · have hnone := decodedMessage_none _ _ dec' hdec' (by rw [hlen, hn30]; exact hc)
    refine ⟨.headerSent { uc := { epoch := e, auth := auth, dk := dkOf K s },
                          sending_ek := enc, receiving_ct1 := dec' }, ?_,
      Or.inl ⟨enc, _, dec', henc, hdec', hc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendEk.HeaderSent.epoch, hlt,
      Chunked.SendEk.HeaderSent.recv_ct1_chunk, spqrPolyApi, hadd, hnone, Except.mapError,
      StatesResult.ofPanic, bind, Except.bind, liftM, monadLift, MonadLift.monadLift,
      liftSpqrPanic]
  · have hsome := decodedMessage_spec _ _ dec' hdec' (by simp [hlen]) (by simp [hlen])
      (by rw [hlen, hn30]; omega)
    refine ⟨.ct1Received { uc := { epoch := e, auth := auth, dk := dkOf K s, ct1 := ct1Of K s r },
                           sending_ek := enc }, ?_,
      Or.inr ⟨enc, henc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendEk.HeaderSent.epoch, hlt,
      Chunked.SendEk.HeaderSent.recv_ct1_chunk, Unchunked.SendEk.EkSent.recv_ct1,
      spqrPolyApi, hadd, hsome, Except.mapError, StatesResult.ofPanic, bind, Except.bind,
      liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

/-- `.headerSent` ignores messages of epoch `< e` and non-`.ct1` messages at epoch `e`. -/
theorem xRecv_hs_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (x : St F) (hx : XHS F K e auth s r x) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ ∀ c, m.payload ≠ .ct1 c)) :
    x.recv K m = .ok { key := none, state := x } := by
  obtain ⟨enc, S, dec, -, -, -, rfl⟩ := hx
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendEk.HeaderSent.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendEk.HeaderSent.epoch]

private theorem wp4_ep_xc1r_decaps_eq_match (K : MlKem) (dk ct1 ct2 : Bytes) :
    decaps K dk ct1 ct2 =
      match (if h1 : ct1.length = CIPHERTEXT1_SIZE then some ⟨ct1, h1⟩ else none),
            (if h2 : ct2.length = CIPHERTEXT2_SIZE then some ⟨ct2, h2⟩ else none),
            (if h3 : dk.length = DECAPSULATION_KEY_SIZE then some ⟨dk, h3⟩ else none) with
      | some ct1Vec, some ct2Vec, some dkVec => .ok (K.decaps dkVec ct1Vec ct2Vec).toList
      | _, _, _ => .error (.decapsBadSize dk.length ct1.length ct2.length) :=
  rfl

private theorem wp4_ep_xc1r_c2Msg_length (F : ShaCompress) (K : MlKem) (e : Epoch)
    (auth : Authenticator) (s : Seed) (r : EncRand) (hk : KemOk K s r) :
    (c2Msg F K e auth s r).length = 160 := by
  obtain ⟨ct2, h2, hdec⟩ := hk.decaps_ok
  rw [wp4_ep_xc1r_decaps_eq_match] at hdec
  have hct2 : ct2.length = 128 := by
    by_contra hne
    simp [CIPHERTEXT2_SIZE, hne] at hdec
  simp [c2Msg, ct2Of, h2, hct2]

/-- `.ct1Received` receiving its first `.ct2` chunk initializes the 160-byte `c2Msg` decoder
and transitions to `XESCR`. -/
theorem xRecv_c1r_ct2 (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hk : KemOk K s r) (x : St F) (hx : XC1R F K e auth s r x)
    (idx : BitVec 16) :
    ∃ x' : St F,
      x.recv K (chunkMsg .ct2 e (c2Msg F K e auth s r) idx) = .ok { key := none, state := x' } ∧
      XESCR F K e auth s r x' := by
  obtain ⟨enc, -, rfl⟩ := hx
  have hlen := wp4_ep_xc1r_c2Msg_length F K e auth s r hk
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  have hdec0 : DecInv (c2Msg F K e auth s r) ∅ (freshDec 160) := by
    have h := decInv_freshDec (c2Msg F K e auth s r) (by rw [hlen])
    rwa [hlen] at h
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (c2Msg F K e auth s r) ∅ (freshDec 160) hdec0 (by rw [hlen]; decide) idx
  have hdecNew : ∀ site n, n = 160 →
      expectDecoderNew spqrPolyApi site n = .ok (freshDec 160) := by
    rintro site n rfl
    simp [expectDecoderNew, spqrPolyApi, decoderNew_eq 160 (by decide), Except.mapError,
      bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
  refine ⟨.ekSentCt1Received { uc := { epoch := e, auth := auth, dk := dkOf K s,
                                       ct1 := ct1Of K s r },
                               receiving_ct2 := dec' }, ?_,
    ⟨insert idx.toNat ∅, dec', hdec', by simp, rfl⟩⟩
  simp only [States.recv, chunkMsg, Chunked.SendEk.Ct1Received.epoch, gt_iff_lt, hlt, ↓reduceIte,
    Chunked.SendEk.Ct1Received.recv_ct2_chunk, bne_self_eq_false, Bool.false_eq_true]
  rw [hdecNew]
  · simp [spqrPolyApi, hadd, Except.mapError, StatesResult.ofPanic, bind, Except.bind,
      liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
  · rfl

/-- `.ct1Received` ignores messages of epoch `< e` and non-`.ct2` messages at epoch `e`. -/
theorem xRecv_c1r_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (x : St F) (hx : XC1R F K e auth s r x) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ ∀ c, m.payload ≠ .ct2 c)) :
    x.recv K m = .ok { key := none, state := x } := by
  obtain ⟨enc, -, rfl⟩ := hx
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendEk.Ct1Received.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendEk.Ct1Received.epoch]

/-- `.ekSentCt1Received` receiving an honest `.ct2` chunk either stays in `XESCR` or decodes
and verifies `c2Msg`, outputs `(e, secOf F K e s r)`, and advances to `XLag` at `e + 1`. -/
theorem xRecv_escr_ct2 (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hk : KemOk K s r) (hepoch : e.toNat + 1 < 2 ^ 64) (x : St F)
    (hx : XESCR F K e auth s r x) (idx : BitVec 16) :
    ∃ x' : St F,
      (x.recv K (chunkMsg .ct2 e (c2Msg F K e auth s r) idx) = .ok { key := none, state := x' } ∧
        XESCR F K e auth s r x') ∨
      (x.recv K (chunkMsg .ct2 e (c2Msg F K e auth s r) idx) =
          .ok { key := some { epoch := e, secret := secOf F K e s r }, state := x' } ∧
        XLag F K e auth s r x') := by
  obtain ⟨S, dec, hdec, -, rfl⟩ := hx
  have hlen := c2Msg_length F K e auth s r hk
  have hn5 : needed 160 0 = 5 := by decide
  have hct1 : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
  have hct2 : (ct2Of K s r).length = 128 := ct2Of_length K s r hk
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (c2Msg F K e auth s r) S dec hdec (by rw [hlen]; decide) idx
  by_cases hc : (insert idx.toNat S).card < 5
  · have hnone := decodedMessage_none _ _ dec' hdec' (by rw [hlen, hn5]; exact hc)
    refine ⟨.ekSentCt1Received { uc := { epoch := e, auth := auth, dk := dkOf K s,
                                         ct1 := ct1Of K s r },
                                 receiving_ct2 := dec' },
      Or.inl ⟨?_, _, dec', hdec', hc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendEk.EkSentCt1Received.epoch, hlt,
      Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk, spqrPolyApi, hadd, hnone,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind]
  · have hsome := decodedMessage_spec _ _ dec' hdec' (by simp [hlen]) (by simp [hlen])
      (by rw [hlen, hn5]; omega)
    have htake : (c2Msg F K e auth s r).take 128 = ct2Of K s r := List.take_left' hct2
    have hdrop : (c2Msg F K e auth s r).drop 128 =
        (authNext F K e auth s r).macCtUnchecked F e (ct1Of K s r ++ ct2Of K s r) :=
      List.drop_left' hct2
    obtain ⟨ct2, h2, hdecaps⟩ := hk.decaps_ok
    have hct2_eq : ct2 = ct2Of K s r := by
      have h2' := encaps2_eq K s r hk
      rw [h2] at h2'
      injection h2'
    rw [hct2_eq] at hdecaps
    have hadd' : spqrPolyApi.add_chunk dec
        (spqrPolyApi.mkChunk idx (chunkData (c2Msg F K e auth s r) idx)) = .ok dec' := by
      simp [spqrPolyApi, hadd, Except.mapError]
    have hsome' : spqrPolyApi.decoded_message dec' = .ok (some (c2Msg F K e auth s r)) := by
      simp [spqrPolyApi, hsome, Except.mapError]
    have hhkdf : ∀ info, info = sckaKeyInfoPrefix ++ be64 e →
        (spqrAuthApi F).hkdf_to_vec (List.replicate 32 0#8) (ss0Of K s r) info 32 =
          .ok (secOf F K e s r) := by
      rintro _ rfl
      simp [spqrAuthApi, hkdfToVec_of_le _ _ _ _ (show 32 ≤ hkdfMaxOkmLen by decide), secOf]
    have hupd : (spqrAuthApi F).update auth e (secOf F K e s r) =
        .ok (authNext F K e auth s r) := rfl
    have hver' : (spqrAuthApi F).verify_ct (authNext F K e auth s r) e
        (ct1Of K s r ++ ct2Of K s r)
        ((authNext F K e auth s r).macCtUnchecked F e (ct1Of K s r ++ ct2Of K s r)) =
        .ok (.ok ()) :=
      verifyCt_macCt F (authNext F K e auth s r)
        (authWf_update F auth e (secOf F K e s r)) e (ct1Of K s r ++ ct2Of K s r)
        (by rw [List.length_append, hct1, hct2]; decide)
    have hne : ¬ e = 18446744073709551615#64 := by
      intro h; rw [h] at hepoch; simp at hepoch
    have hdec96 : ∀ loc n, n = 96 →
        expectDecoderNew spqrPolyApi loc n = .ok (freshDec 96) := by
      rintro loc n rfl
      simp only [expectDecoderNew, spqrPolyApi, decoderNew_eq 96 (by decide), Except.mapError,
        bind, Except.bind]
      rfl
    refine ⟨.noHeaderReceived { uc := { epoch := e + 1#64, auth := authNext F K e auth s r },
                                receiving_hdr := freshDec 96 },
      Or.inr ⟨?_, rfl⟩⟩
    simp only [States.recv, chunkMsg, Chunked.SendEk.EkSentCt1Received.epoch, hlt, ↓reduceIte,
      Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk, bne_self_eq_false, Bool.false_eq_true,
      hadd', hsome', StatesResult.ofPanic, CIPHERTEXT2_SIZE, hlen, htake, hdrop,
      Unchunked.SendEk.EkSentCt1Received.recv_ct2, hdecaps, bind, Except.bind]
    rw [hhkdf, hdec96]
    · simp [hupd, hver', hne]
    · rfl
    · rfl

/-- `.ekSentCt1Received` ignores messages of epoch `< e` and non-`.ct2` messages at epoch `e`. -/
theorem xRecv_escr_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (x : St F) (hx : XESCR F K e auth s r x) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ ∀ c, m.payload ≠ .ct2 c)) :
    x.recv K m = .ok { key := none, state := x } := by
  obtain ⟨S, dec, -, -, rfl⟩ := hx
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendEk.EkSentCt1Received.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendEk.EkSentCt1Received.epoch]

/-- `XLag` (at `e + 1`) ignores all messages with `m.epoch ≤ e`. -/
theorem xRecv_lag (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hepoch : e.toNat + 1 < 2 ^ 64) (x : St F) (hx : XLag F K e auth s r x)
    (m : Msg) (hm : m.epoch ≤ e) :
    x.recv K m = .ok { key := none, state := x } := by
  have he1 : (e + 1#64).toNat = e.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have hlt : m.epoch < e + 1#64 := by
    simp only [BitVec.lt_def, BitVec.le_def, he1] at hm ⊢; omega
  have hgt : ¬ e + 1#64 < m.epoch := by
    simp only [BitVec.lt_def, BitVec.le_def, he1] at hm ⊢; omega
  subst hx
  simp [States.recv, Chunked.SendCt.NoHeaderReceived.epoch, hlt, hgt]

/-! ## CT-side (`Y_e`) send transitions -/

/-- `.headerReceived` draws 32 encapsulation bytes `r`, outputs `(e, secOf F K e s r)`,
updates `auth` to `authNext`, and transitions to `YC1S` emitting `.ct1` chunk `0`. -/
theorem ySend_hr (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) (tape : Bytes) (hr : r.toList = tape.take 32) :
    let y : St F := .headerReceived { uc := { epoch := e, auth := auth, hdr := hdrOf K s },
                                      receiving_ek := freshDec 1152 }
    ∃ y' : St F,
      y.send K tape = .ok ({ msg := chunkMsg .ct1 e (ct1Of K s r) 0#16,
                             key := some { epoch := e, secret := secOf F K e s r },
                             state := y' }, tape.drop 32) ∧
      YC1S F K e auth s r y' := by
  intro y
  have h32 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := by
    simp [SHARED_SECRET_SIZE, ← hr]
  have hr_eq : (⟨tape.take SHARED_SECRET_SIZE, h32⟩ : EncRand) = r := by
    apply Subtype.ext
    exact hr.symm
  obtain ⟨⟨ct1, es, ss⟩, hencOf⟩ := Option.ne_none_iff_exists'.1 hk.encaps1_ok
  have hct1 : ct1Of K s r = ct1.toList := by simp [ct1Of, hencOf]
  have hes : esOf K s r = es.toList := by simp [esOf, hencOf]
  have hss : ss0Of K s r = ss.toList := by simp [ss0Of, hencOf]
  have henc1 : encaps1 K (hdrOf K s) tape =
      .ok ((ct1Of K s r, esOf K s r, ss0Of K s r), tape.drop 32) := by
    have henc' : K.encaps1 (hdrOf K s) r = some (ct1, es, ss) := hencOf
    rw [encaps1_eq_match, dite_eq_left h32, hr_eq]
    dsimp only
    rw [henc', hct1, hes, hss]
    rfl
  have hct1_len : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
  have henc := encodeBytes_spec (ct1Of K s r) (by simp [hct1_len]) (by simp [hct1_len])
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (ct1Of K s r)
      { idx := 0#32, s := .points (msgPoints (ct1Of K s r)) }
      (Or.inl rfl) (by simp [hct1_len])
  have h0 : (0#32).setWidth 16 = 0#16 := by decide
  simp only [h0] at hnext
  have hdec : DecInv (ekOf K s) ∅ (freshDec 1152) := by
    simpa [ekOf_length] using decInv_freshDec (ekOf K s) (by simp [ekOf_length])
  refine ⟨.ct1Sampled { uc := { epoch := e, auth := authNext F K e auth s r, hdr := hdrOf K s,
                                es := esOf K s r, ct1 := ct1Of K s r },
                        sending_ct1 := enc', receiving_ek := freshDec 1152 },
    ?_, enc', ∅, freshDec 1152, henc', hdec, by decide, rfl⟩
  simp only [y, States.send, Chunked.SendCt.HeaderReceived.send_ct1_chunk,
    Unchunked.SendCt.HeaderReceived.send_ct1, henc1, spqrAuthApi,
    hkdfToVec_of_le _ _ _ _ (show 32 ≤ hkdfMaxOkmLen by decide), expectEncodeBytes, spqrPolyApi,
    henc, hnext, Except.mapError, StatesResult.ofPanic, bind, Except.bind,
    liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
    Chunked.SendCt.HeaderReceived.epoch, chunkMsg, secOf, authNext, be64]
  rfl

/-- `.ct1Sampled` emits the next `.ct1` chunk and preserves `YC1S`. -/
theorem ySend_c1s (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) (hy : YC1S F K e auth s r y) (tape : Bytes) :
    ∃ (idx : BitVec 16) (y' : St F),
      y.send K tape = .ok ({ msg := chunkMsg .ct1 e (ct1Of K s r) idx, key := none,
                             state := y' }, tape) ∧ YC1S F K e auth s r y' := by
  obtain ⟨enc, S, dec, henc, hdec, hS, rfl⟩ := hy
  have hle := ct1Of_length_le K s r
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (ct1Of K s r) enc henc (by omega)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', S, dec, henc', hdec, hS, rfl⟩
  simp only [States.send, Chunked.SendCt.Ct1Sampled.send_ct1_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic, Chunked.SendCt.Ct1Sampled.epoch]
  rfl

/-- `.ekReceivedCt1Sampled` emits the next `.ct1` chunk and preserves `YEkR`. -/
theorem ySend_ekr (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) (hy : YEkR F K e auth s r y) (tape : Bytes) :
    ∃ (idx : BitVec 16) (y' : St F),
      y.send K tape = .ok ({ msg := chunkMsg .ct1 e (ct1Of K s r) idx, key := none,
                             state := y' }, tape) ∧ YEkR F K e auth s r y' := by
  obtain ⟨enc, henc, rfl⟩ := hy
  have hle := ct1Of_length_le K s r
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (ct1Of K s r) enc henc (by omega)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', henc', rfl⟩
  simp only [States.send, Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic,
    Chunked.SendCt.EkReceivedCt1Sampled.epoch]
  rfl

/-- `.ct1Acknowledged` emits `noneMsg e` and leaves the state unchanged. -/
theorem ySend_c1a (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (y : St F) (hy : YC1A F K e auth s r y) (tape : Bytes) :
    y.send K tape = .ok ({ msg := noneMsg e, key := none, state := y }, tape) := by
  obtain ⟨S, dec, -, -, rfl⟩ := hy
  rfl

/-- `.ct2Sampled` emits the next `.ct2` chunk and preserves `YC2S`. -/
theorem ySend_c2s (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) (y : St F) (hy : YC2S F K e auth s r y) (tape : Bytes) :
    ∃ (idx : BitVec 16) (y' : St F),
      y.send K tape = .ok ({ msg := chunkMsg .ct2 e (c2Msg F K e auth s r) idx, key := none,
                             state := y' }, tape) ∧ YC2S F K e auth s r y' := by
  obtain ⟨enc, henc, rfl⟩ := hy
  have hct2 : (ct2Of K s r).length = 128 := by
    obtain ⟨ct2, h2, hdec⟩ := hk.decaps_ok
    change (match (if h1 : (ct1Of K s r).length = 960 then some (⟨_, h1⟩ : List.Vector (BitVec 8) 960) else none),
                  (if h2 : ct2.length = 128 then some (⟨_, h2⟩ : List.Vector (BitVec 8) 128) else none),
                  (if h3 : (dkOf K s).length = 2400 then some (⟨_, h3⟩ : List.Vector (BitVec 8) 2400) else none) with
            | some a, some b, some c => Except.ok (K.decaps c a b).toList
            | _, _, _ => Except.error (StatesPanic.decapsBadSize (dkOf K s).length (ct1Of K s r).length ct2.length)) =
        .ok (ss0Of K s r) at hdec
    have hct2_eq : ct2Of K s r = ct2 := by simp [ct2Of, h2]
    rw [hct2_eq]
    by_contra hne
    simp [hne] at hdec
  have hc2 : (c2Msg F K e auth s r).length = 160 := by simp [c2Msg, hct2]
  obtain ⟨enc', hnext, henc', -⟩ :=
    nextChunk_spec (c2Msg F K e auth s r) enc henc (by rw [hc2]; decide)
  refine ⟨enc.idx.setWidth 16, _, ?_, enc', henc', rfl⟩
  simp only [States.send, Chunked.SendCt.Ct2Sampled.send_ct2_chunk, spqrPolyApi, hnext,
    Except.mapError, bind, Except.bind, StatesResult.ofPanic, Chunked.SendCt.Ct2Sampled.epoch]
  rfl

/-! ## CT-side (`Y_e`) receive transitions -/

/-- `.ct1Sampled` receiving an `.ek` chunk stays in `YC1S` or decodes `ek` and moves to `YEkR`. -/
theorem yRecv_c1s_ek (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator) (s : Seed)
    (r : EncRand) (hk : KemOk K s r) (y : St F) (hy : YC1S F K e auth s r y) (idx : BitVec 16) :
    ∃ y' : St F, y.recv K (chunkMsg .ek e (ekOf K s) idx) = .ok { key := none, state := y' } ∧
      (YC1S F K e auth s r y' ∨ YEkR F K e auth s r y') := by
  obtain ⟨enc, S, dec, henc, hdec, _hS, rfl⟩ := hy
  have hlen : (ekOf K s).length = 1152 := ekOf_length K s
  have hn36 : needed 1152 0 = 36 := by decide
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (ekOf K s) S dec hdec (by rw [hlen]; decide) idx
  by_cases hc : (insert idx.toNat S).card < 36
  · have hnone := decodedMessage_none _ _ dec' hdec' (by rw [hlen, hn36]; exact hc)
    refine ⟨.ct1Sampled { uc := { epoch := e, auth := authNext F K e auth s r, hdr := hdrOf K s,
                                  es := esOf K s r, ct1 := ct1Of K s r },
                          sending_ct1 := enc, receiving_ek := dec' }, ?_,
      Or.inl ⟨enc, _, dec', henc, hdec', hc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Sampled.epoch, hlt,
      Chunked.SendCt.Ct1Sampled.recv_ek_chunk, spqrPolyApi, hadd, hnone,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind]
  · have hsome := decodedMessage_spec _ _ dec' hdec' (by simp [hlen]) (by simp [hlen])
      (by rw [hlen, hn36]; omega)
    refine ⟨.ekReceivedCt1Sampled { uc := { epoch := e, auth := authNext F K e auth s r,
                                            es := esOf K s r, ek := ekOf K s, ct1 := ct1Of K s r },
                                    sending_ct1 := enc }, ?_,
      Or.inr ⟨enc, henc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Sampled.epoch, hlt,
      Chunked.SendCt.Ct1Sampled.recv_ek_chunk, spqrPolyApi, hadd, hsome,
      Unchunked.SendCt.Ct1Sent.recv_ek, hk.ek_matches,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind]

/-- `.ct1Sampled` receiving an `.ekCt1Ack` chunk moves to `YC1A` or decodes `ek`, runs
`encaps2`, and moves to `YC2S`. -/
theorem yRecv_c1s_ekAck (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hk : KemOk K s r) (y : St F) (hy : YC1S F K e auth s r y)
    (idx : BitVec 16) :
    ∃ y' : St F,
      y.recv K (chunkMsg .ekCt1Ack e (ekOf K s) idx) = .ok { key := none, state := y' } ∧
      (YC1A F K e auth s r y' ∨ YC2S F K e auth s r y') := by
  obtain ⟨enc, S, dec, _henc, hdec, _hS, rfl⟩ := hy
  have hlen : (ekOf K s).length = 1152 := ekOf_length K s
  have hn36 : needed 1152 0 = 36 := by decide
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  obtain ⟨dec', hadd, hdec'⟩ :=
    addChunk_spec (ekOf K s) S dec hdec (by rw [hlen]; decide) idx
  by_cases hc : (insert idx.toNat S).card < 36
  · have hnone := decodedMessage_none _ _ dec' hdec' (by rw [hlen, hn36]; exact hc)
    refine ⟨.ct1Acknowledged { uc := { epoch := e, auth := authNext F K e auth s r,
                                       hdr := hdrOf K s, es := esOf K s r, ct1 := ct1Of K s r },
                               receiving_ek := dec' }, ?_,
      Or.inl ⟨_, dec', hdec', hc, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Sampled.epoch, hlt,
      Chunked.SendCt.Ct1Sampled.recv_ek_chunk, spqrPolyApi, hadd, hnone,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind]
  · have hsome := decodedMessage_spec _ _ dec' hdec' (by simp [hlen]) (by simp [hlen])
      (by rw [hlen, hn36]; omega)
    have henc2 := encaps2_eq K s r hk
    have hct1 : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
    have hct2 : (ct2Of K s r).length = 128 := ct2Of_length K s r hk
    have hmac := macCt_eq F (authNext F K e auth s r)
      (authWf_update F auth e (secOf F K e s r)) e (ct1Of K s r ++ ct2Of K s r)
      (by simp only [List.length_append, hct1, hct2]; decide)
    have hc2len := c2Msg_length F K e auth s r hk
    have hencC2 := encodeBytes_spec (c2Msg F K e auth s r) (by simp [hc2len]) (by simp [hc2len])
    simp only [c2Msg] at hencC2
    refine ⟨.ct2Sampled { uc := { epoch := e, auth := authNext F K e auth s r },
                          sending_ct2 := { idx := 0#32, s := .points (msgPoints (c2Msg F K e auth s r)) } }, ?_,
      Or.inr ⟨_, Or.inl rfl, rfl⟩⟩
    simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Sampled.epoch, hlt,
      Chunked.SendCt.Ct1Sampled.recv_ek_chunk, spqrPolyApi, spqrAuthApi, hadd, hsome,
      Unchunked.SendCt.Ct1Sent.recv_ek, hk.ek_matches,
      Unchunked.SendCt.Ct1SentEkReceived.send_ct2, henc2, hmac,
      Chunked.SendCt.send_ct2_encoder, expectEncodeBytes, hencC2, c2Msg,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind,
      liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

/-- `.ct1Sampled` ignores messages of epoch `< e` and non-`ek`/`ekCt1Ack` messages at `e`. -/
theorem yRecv_c1s_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (y : St F) (hy : YC1S F K e auth s r y) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ (∀ c, m.payload ≠ .ek c) ∧ ∀ c, m.payload ≠ .ekCt1Ack c)) :
    y.recv K m = .ok { key := none, state := y } := by
  obtain ⟨enc, S, dec, -, -, -, rfl⟩ := hy
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h1, h2⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendCt.Ct1Sampled.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendCt.Ct1Sampled.epoch]

/-- `.ekReceivedCt1Sampled` receiving `ackMsg e` or an `.ekCt1Ack` chunk runs `encaps2` and
transitions to `YC2S`. -/
theorem yRecv_ekr_ack (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hk : KemOk K s r) (y : St F) (hy : YEkR F K e auth s r y) (m : Msg)
    (hm : m = ackMsg e ∨ ∃ idx, m = chunkMsg .ekCt1Ack e (ekOf K s) idx) :
    ∃ y' : St F, y.recv K m = .ok { key := none, state := y' } ∧ YC2S F K e auth s r y' := by
  obtain ⟨enc, -, rfl⟩ := hy
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  have hct2 : encaps2 K (ekOf K s) (esOf K s r) = .ok (ct2Of K s r) := encaps2_eq K s r hk
  have hmac := macCt_eq F (authNext F K e auth s r) (authWf_update F auth e (secOf F K e s r)) e
    (ct1Of K s r ++ ct2Of K s r) (by simp [ct1Of_length K s r hk, ct2Of_length K s r hk])
  have hc2len : (c2Msg F K e auth s r).length = 160 := c2Msg_length F K e auth s r hk
  have henc2 : PolyEncoder.encodeBytes
      (ct2Of K s r ++ (authNext F K e auth s r).macCtUnchecked F e (ct1Of K s r ++ ct2Of K s r)) =
      .ok (.ok { idx := 0#32, s := .points (msgPoints (c2Msg F K e auth s r)) }) :=
    encodeBytes_spec (c2Msg F K e auth s r) (by simp [hc2len]) (by simp [hc2len])
  refine ⟨.ct2Sampled { uc := { epoch := e, auth := authNext F K e auth s r },
                        sending_ct2 := { idx := 0#32, s := .points (msgPoints (c2Msg F K e auth s r)) } },
    ?_, ⟨_, Or.inl rfl, rfl⟩⟩
  rcases hm with rfl | ⟨idx, rfl⟩ <;>
    simp [States.recv, ackMsg, chunkMsg, Chunked.SendCt.EkReceivedCt1Sampled.epoch, hlt,
      Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack, Unchunked.SendCt.Ct1SentEkReceived.send_ct2,
      Chunked.SendCt.send_ct2_encoder, expectEncodeBytes, spqrPolyApi, spqrAuthApi,
      Except.mapError, StatesResult.ofPanic, bind, Except.bind,
      liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
      hct2, hmac, henc2]

/-- `.ekReceivedCt1Sampled` ignores messages of epoch `≤ e` that carry no `ct1` acknowledgment. -/
theorem yRecv_ekr_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (y : St F) (hy : YEkR F K e auth s r y) (m : Msg)
    (hm : m.epoch < e ∨
      (m.epoch = e ∧ m.payload ≠ .ct1Ack true ∧ ∀ c, m.payload ≠ .ekCt1Ack c)) :
    y.recv K m = .ok { key := none, state := y } := by
  obtain ⟨enc, -, rfl⟩ := hy
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h1, h2⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch, hle, h]
  · cases pl with
    | ct1Ack b => cases b <;> simp_all [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch]
    | _ => simp_all [States.recv, Chunked.SendCt.EkReceivedCt1Sampled.epoch]

/-- `.ct1Acknowledged` receiving an `.ek` or `.ekCt1Ack` chunk stays in `YC1A` or decodes `ek`,
runs `encaps2`, and transitions to `YC2S`. -/
theorem yRecv_c1a_ek (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hk : KemOk K s r) (y : St F) (hy : YC1A F K e auth s r y)
    (pl : spqrPolyApi.Chunk → MessagePayload spqrPolyApi)
    (hpl : pl = MessagePayload.ek ∨ pl = MessagePayload.ekCt1Ack) (idx : BitVec 16) :
    ∃ y' : St F, y.recv K (chunkMsg pl e (ekOf K s) idx) = .ok { key := none, state := y' } ∧
      (YC1A F K e auth s r y' ∨ YC2S F K e auth s r y') := by
  obtain ⟨S, dec, hdec, -, rfl⟩ := hy
  have hlt : ¬ e < e := BitVec.lt_irrefl e
  have heklen : (ekOf K s).length = 1152 := ekOf_length K s
  obtain ⟨dec', hadd, hdec'⟩ := addChunk_spec (ekOf K s) S dec hdec (by simp [heklen]) idx
  have hneed : needed (ekOf K s).length 0 = 36 := by rw [heklen]; decide
  by_cases hc : (insert idx.toNat S).card < 36
  · have hdm := decodedMessage_none (ekOf K s) (insert idx.toNat S) dec' hdec' (by rw [hneed]; exact hc)
    refine ⟨.ct1Acknowledged { uc := { epoch := e, auth := authNext F K e auth s r,
                                       hdr := hdrOf K s, es := esOf K s r, ct1 := ct1Of K s r },
                               receiving_ek := dec' },
      ?_, Or.inl ⟨insert idx.toNat S, dec', hdec', hc, rfl⟩⟩
    rcases hpl with rfl | rfl <;>
      simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Acknowledged.epoch, hlt,
        Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk, spqrPolyApi, Except.mapError,
        StatesResult.ofPanic, bind, Except.bind, hadd, hdm]
  · have hdm := decodedMessage_spec (ekOf K s) (insert idx.toNat S) dec' hdec'
        (by simp [heklen]) (by simp [heklen]) (by rw [hneed]; omega)
    have hct2 : encaps2 K (ekOf K s) (esOf K s r) = .ok (ct2Of K s r) := encaps2_eq K s r hk
    have hmac := macCt_eq F (authNext F K e auth s r) (authWf_update F auth e (secOf F K e s r)) e
      (ct1Of K s r ++ ct2Of K s r) (by simp [ct1Of_length K s r hk, ct2Of_length K s r hk])
    have hc2len : (c2Msg F K e auth s r).length = 160 := c2Msg_length F K e auth s r hk
    have henc2 : PolyEncoder.encodeBytes
        (ct2Of K s r ++ (authNext F K e auth s r).macCtUnchecked F e (ct1Of K s r ++ ct2Of K s r)) =
        .ok (.ok { idx := 0#32, s := .points (msgPoints (c2Msg F K e auth s r)) }) :=
      encodeBytes_spec (c2Msg F K e auth s r) (by simp [hc2len]) (by simp [hc2len])
    refine ⟨.ct2Sampled { uc := { epoch := e, auth := authNext F K e auth s r },
                          sending_ct2 := { idx := 0#32, s := .points (msgPoints (c2Msg F K e auth s r)) } },
      ?_, Or.inr ⟨_, Or.inl rfl, rfl⟩⟩
    rcases hpl with rfl | rfl <;>
      simp [States.recv, chunkMsg, Chunked.SendCt.Ct1Acknowledged.epoch, hlt,
        Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk, Unchunked.SendCt.Ct1Sent.recv_ek,
        hk.ek_matches, Unchunked.SendCt.Ct1SentEkReceived.send_ct2,
        Chunked.SendCt.send_ct2_encoder, expectEncodeBytes, spqrPolyApi, spqrAuthApi,
        Except.mapError, StatesResult.ofPanic, bind, Except.bind,
        liftM, monadLift, MonadLift.monadLift, liftSpqrPanic,
        hadd, hdm, hct2, hmac, henc2]

/-- `.ct1Acknowledged` ignores messages of epoch `< e` and non-`ek`/`ekCt1Ack` messages at `e`. -/
theorem yRecv_c1a_ignore (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (y : St F) (hy : YC1A F K e auth s r y) (m : Msg)
    (hm : m.epoch < e ∨ (m.epoch = e ∧ (∀ c, m.payload ≠ .ek c) ∧ ∀ c, m.payload ≠ .ekCt1Ack c)) :
    y.recv K m = .ok { key := none, state := y } := by
  obtain ⟨S, dec, -, -, rfl⟩ := hy
  obtain ⟨me, pl⟩ := m
  rcases hm with h | ⟨rfl, h1, h2⟩
  · have hle : ¬ e < me := by simp only [BitVec.lt_def] at h ⊢; omega
    simp [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, hle, h]
  · cases pl <;> simp_all [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch]

/-- `.ct2Sampled` ignores all messages with `m.epoch ≤ e`. -/
theorem yRecv_c2s_old (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (y : St F) (hy : YC2S F K e auth s r y) (m : Msg) (hm : m.epoch ≤ e) :
    y.recv K m = .ok { key := none, state := y } := by
  obtain ⟨enc, -, rfl⟩ := hy
  have hle : ¬ e < m.epoch := by simp only [BitVec.lt_def, BitVec.le_def] at hm ⊢; omega
  simp [States.recv, Chunked.SendCt.Ct2Sampled.epoch, hle]

/-- `.ct2Sampled` receiving `noneMsg (e + 1)` advances to `.keysUnsampled` at `e + 1` with
`authNext`. -/
theorem yRecv_c2s_next (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (r : EncRand) (hepoch : e.toNat + 1 < 2 ^ 64) (y : St F)
    (hy : YC2S F K e auth s r y) :
    y.recv K (noneMsg (e + 1#64)) =
      .ok { key := none,
            state := .keysUnsampled { uc := { epoch := e + 1#64,
                                              auth := authNext F K e auth s r } } } := by
  have he1 : (e + 1#64).toNat = e.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have hlt : e < e + 1#64 := by simp only [BitVec.lt_def, he1]; omega
  have hne : ¬ e = 18446744073709551615#64 := by
    intro h; rw [h] at hepoch; simp at hepoch
  obtain ⟨enc, -, rfl⟩ := hy
  simp [States.recv, noneMsg, Chunked.SendCt.Ct2Sampled.epoch, hlt, hne,
    Chunked.SendCt.Ct2Sampled.recv_next_epoch, Unchunked.SendCt.Ct2Sent.recv_next_epoch,
    StatesResult.ofPanic, bind, Except.bind]

/-! ## Protobuf round-trip for full-epoch shapes -/

/-- All reachable EK-side shapes in `XShapeE` round-trip through `States.from_pb ∘ into_pb`. -/
theorem xShapeE_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (hkem : ∀ s r, c = .both s r → KemOk K s r) (x : St F)
    (hx : XShapeE F K e auth c x) :
    States.from_pb spqrPolyApi (spqrAuthApi F) x.into_pb = .ok x := by
  cases c with
  | init => exact xShape_codec F K e auth none x hx
  | seed s => exact xShape_codec F K e auth (some s) x hx
  | both s r =>
    have hk : KemOk K s r := hkem s r rfl
    have hct1 : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
    rcases hx with hx | ⟨enc, S, dec, henc, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩ |
      ⟨S, dec, hdec, -, rfl⟩ | hx
    · exact xShape_codec F K e auth (some s) x hx
    · have hpts : dec.ptsNeeded = 480 := by rw [hdec.ptsNeeded, hct1]
      have hptsPb : (spqrPolyApi.decoder_into_pb dec).ptsNeeded = 480#32 := by
        simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpts]
      have hencPb :
          encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
        Codec.encoderFromPbStateDecode_of_encInv henc (by rw [ekOf_length]; decide)
          (by rw [ekOf_length]; decide)
      have hdecPb :
          decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec :=
        Codec.decoderFromPbStateDecode_of_decInv hdec (by rw [hct1]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendEk.HeaderSent.into_pb, Chunked.SendEk.HeaderSent.from_pb,
        Unchunked.SendEk.EkSent.into_pb, Unchunked.SendEk.EkSent.from_pb,
        Codec.dkOf_length, hptsPb, hencPb, hdecPb, Codec.auth_from_into, bind, Except.bind]
      rfl
    · have hencPb :
          encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
        Codec.encoderFromPbStateDecode_of_encInv henc (by rw [ekOf_length]; decide)
          (by rw [ekOf_length]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendEk.Ct1Received.into_pb, Chunked.SendEk.Ct1Received.from_pb,
        Unchunked.SendEk.EkSentCt1Received.into_pb, Unchunked.SendEk.EkSentCt1Received.from_pb,
        Codec.dkOf_length, hct1, hencPb, Codec.auth_from_into, bind, Except.bind]
      rfl
    · obtain ⟨ct2, h2, h3⟩ := hk.decaps_ok
      have hdecaps : decaps K (dkOf K s) (ct1Of K s r) ct2 =
          match (if h : (ct1Of K s r).length = 960 then some ⟨ct1Of K s r, h⟩ else none),
                (if h : ct2.length = 128 then some ⟨ct2, h⟩ else none),
                (if h : (dkOf K s).length = 2400 then some ⟨dkOf K s, h⟩ else none) with
          | some ct1Vec, some ct2Vec, some dkVec => .ok (K.decaps dkVec ct1Vec ct2Vec).toList
          | _, _, _ =>
            .error (.decapsBadSize (dkOf K s).length (ct1Of K s r).length ct2.length) := rfl
      have hct2 : ct2.length = 128 := by
        by_contra hne; rw [hdecaps] at h3; simp [hct1, hne] at h3
      have hc2 : (c2Msg F K e auth s r).length = 160 := by simp [c2Msg, ct2Of, h2, hct2]
      have hpts : dec.ptsNeeded = 80 := by rw [hdec.ptsNeeded, hc2]
      have hptsPb : (spqrPolyApi.decoder_into_pb dec).ptsNeeded = 80#32 := by
        simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpts]
      have hdecPb :
          decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec :=
        Codec.decoderFromPbStateDecode_of_decInv hdec (by rw [hc2]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendEk.EkSentCt1Received.into_pb, Chunked.SendEk.EkSentCt1Received.from_pb,
        Unchunked.SendEk.EkSentCt1Received.into_pb, Unchunked.SendEk.EkSentCt1Received.from_pb,
        Codec.dkOf_length, hct1, hptsPb, hdecPb, Codec.auth_from_into, bind, Except.bind]
      rfl
    · exact yShape_codec F K (e + 1#64) (authNext F K e auth s r) none x hx

/-- All reachable CT-side shapes in `YShapeE` round-trip through `States.from_pb ∘ into_pb`. -/
theorem yShapeE_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (hkem : ∀ s r, c = .both s r → KemOk K s r) (y : St F)
    (hy : YShapeE F K e auth c y) :
    States.from_pb spqrPolyApi (spqrAuthApi F) y.into_pb = .ok y := by
  cases c with
  | init => exact yShape_codec F K e auth none y hy
  | seed s => exact yShape_codec F K e auth (some s) y hy
  | both s r =>
    have hk : KemOk K s r := hkem s r rfl
    have hct1 : (ct1Of K s r).length = 960 := ct1Of_length K s r hk
    have hes : (esOf K s r).length = 2080 := esOf_length K s r hk
    rcases hy with ⟨enc, S, dec, henc, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩ |
      ⟨S, dec, hdec, -, rfl⟩ | ⟨enc, henc, rfl⟩
    · have hpts : dec.ptsNeeded = 576 := by rw [hdec.ptsNeeded, ekOf_length]
      have hptsPb : (spqrPolyApi.decoder_into_pb dec).ptsNeeded = 576#32 := by
        simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpts]
      have hencPb :
          encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
        Codec.encoderFromPbStateDecode_of_encInv henc (by rw [hct1]; decide) (by rw [hct1]; decide)
      have hdecPb :
          decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec :=
        Codec.decoderFromPbStateDecode_of_decInv hdec (by rw [ekOf_length]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendCt.Ct1Sampled.into_pb, Chunked.SendCt.Ct1Sampled.from_pb,
        Unchunked.SendCt.Ct1Sent.into_pb, Unchunked.SendCt.Ct1Sent.from_pb,
        Codec.hdrOf_length, hes, hct1, hptsPb, hencPb, hdecPb, Codec.auth_from_into,
        bind, Except.bind]
      rfl
    · have hencPb :
          encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
        Codec.encoderFromPbStateDecode_of_encInv henc (by rw [hct1]; decide) (by rw [hct1]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendCt.EkReceivedCt1Sampled.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
        Unchunked.SendCt.Ct1SentEkReceived.into_pb, Unchunked.SendCt.Ct1SentEkReceived.from_pb,
        hes, hct1, ekOf_length, hencPb, Codec.auth_from_into, bind, Except.bind]
      rfl
    · have hpts : dec.ptsNeeded = 576 := by rw [hdec.ptsNeeded, ekOf_length]
      have hptsPb : (spqrPolyApi.decoder_into_pb dec).ptsNeeded = 576#32 := by
        simp [spqrPolyApi, protoPolyDecoderToPb, PolyDecoder.intoPb, hpts]
      have hdecPb :
          decoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.decoder_into_pb dec)) = .ok dec :=
        Codec.decoderFromPbStateDecode_of_decInv hdec (by rw [ekOf_length]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendCt.Ct1Acknowledged.into_pb, Chunked.SendCt.Ct1Acknowledged.from_pb,
        Unchunked.SendCt.Ct1Sent.into_pb, Unchunked.SendCt.Ct1Sent.from_pb,
        Codec.hdrOf_length, hes, hct1, hptsPb, hdecPb, Codec.auth_from_into, bind, Except.bind]
      rfl
    · obtain ⟨ct2, h2, h3⟩ := hk.decaps_ok
      have hdecaps : decaps K (dkOf K s) (ct1Of K s r) ct2 =
          match (if h : (ct1Of K s r).length = 960 then some ⟨ct1Of K s r, h⟩ else none),
                (if h : ct2.length = 128 then some ⟨ct2, h⟩ else none),
                (if h : (dkOf K s).length = 2400 then some ⟨dkOf K s, h⟩ else none) with
          | some ct1Vec, some ct2Vec, some dkVec => .ok (K.decaps dkVec ct1Vec ct2Vec).toList
          | _, _, _ =>
            .error (.decapsBadSize (dkOf K s).length (ct1Of K s r).length ct2.length) := rfl
      have hct2 : ct2.length = 128 := by
        by_contra hne; rw [hdecaps] at h3; simp [hct1, hne] at h3
      have hc2 : (c2Msg F K e auth s r).length = 160 := by simp [c2Msg, ct2Of, h2, hct2]
      have hencPb :
          encoderFromPbStateDecode spqrPolyApi (some (spqrPolyApi.encoder_into_pb enc)) = .ok enc :=
        Codec.encoderFromPbStateDecode_of_encInv henc (by rw [hc2]; decide) (by rw [hc2]; decide)
      simp only [States.into_pb, States.from_pb,
        Chunked.SendCt.Ct2Sampled.into_pb, Chunked.SendCt.Ct2Sampled.from_pb,
        Unchunked.SendCt.Ct2Sent.into_pb, Unchunked.SendCt.Ct2Sent.from_pb,
        hencPb, Codec.auth_from_into, bind, Except.bind]
      rfl

/-! ## Epoch-level assembly -/

/-- `States.init_a` and `States.init_b` satisfy `InSyncE` at epoch `1` with `.init` coins. -/
theorem inSyncE_init (F : ShaCompress) (K : MlKem) (authKey : Bytes) :
    ∃ x y : St F, States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok x ∧
      States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok y ∧
      InSyncE F K 1#64 (Authenticator.new F authKey 1#64) .init x y [] [] := by
  obtain ⟨x, y, hx, hy, h⟩ := inSync1_init F K authKey
  exact ⟨x, y, hx, hy, by decide, h.hauth, h.hx, h.hy, by simp, by simp, by simp, by simp, by simp⟩

/-- EK-side send preserves `InSyncE` on any coin tape of length `≥ 64`. -/
theorem inSyncE_sendX (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (tape : Bytes) (htape : 64 ≤ tape.length) :
    ∃ (c' : Coins) (m : Msg) (x' : St F) (tape' : Bytes),
      x.send K tape = .ok ({ msg := m, key := none, state := x' }, tape') ∧
      (c' = c ∨ (c = .init ∧ ∃ s : Seed, s.toList = tape.take 64 ∧ c' = .seed s)) ∧
      InSyncE F K e auth c' x' y (toY ++ [m]) toX := by
  cases c with
  | init =>
    obtain ⟨s, hs, x', hsend, hx'⟩ := xSend_unsampled F K e auth h.hauth x h.hx tape htape
    refine ⟨.seed s, _, x', _, hsend, Or.inr ⟨rfl, s, hs, rfl⟩,
      h.hepoch, h.hauth, hx', yShape_some_of_none F K e auth y h.hy s,
      by simp, by simp, ?_, ?_, ?_⟩
    · intro hmem
      rcases List.mem_append.1 hmem with hmem | hmem
      · obtain ⟨_, _, ⟨⟩, -⟩ := h.hlag hmem
      · simp [noneMsg, hdrChunkMsg] at hmem
    · intro m' hm'
      rcases List.mem_append.1 hm' with hm' | hm'
      · rcases h.htoY m' hm' with hlt | ⟨_, ⟨⟩, -⟩ | ⟨_, _, ⟨⟩, -⟩ | rfl
        · exact Or.inl hlt
        · exact Or.inr (Or.inr (Or.inr rfl))
      · rw [List.mem_singleton] at hm'
        subst hm'
        exact Or.inr (Or.inl ⟨s, rfl, 0#16, rfl⟩)
    · intro m' hm'
      rcases h.htoX m' hm' with hlt | rfl | ⟨_, _, ⟨⟩, -⟩
      · exact Or.inl hlt
      · exact Or.inr (Or.inl rfl)
  | seed s =>
    obtain ⟨idx, x', hsend, hx'⟩ := xSend_sampled F K e auth s x h.hx tape
    refine ⟨.seed s, _, x', _, hsend, Or.inl rfl,
      h.hepoch, h.hauth, hx', h.hy, h.hkem, by simp, ?_, ?_, h.htoX⟩
    · intro hmem
      rcases List.mem_append.1 hmem with hmem | hmem
      · obtain ⟨_, _, ⟨⟩, -⟩ := h.hlag hmem
      · simp [noneMsg, hdrChunkMsg] at hmem
    · intro m' hm'
      rcases List.mem_append.1 hm' with hm' | hm'
      · exact h.htoY m' hm'
      · rw [List.mem_singleton] at hm'
        subst hm'
        exact Or.inr (Or.inl ⟨s, rfl, idx, rfl⟩)
  | both s r =>
    have hnot_escr_lag : ∀ z : St F,
        (XShape F K e auth (some s) z ∨ XHS F K e auth s r z ∨ XC1R F K e auth s r z) →
        ∀ s' r', ¬ XESCR F K e auth s' r' z ∧ ¬ XLag F K e auth s' r' z := by
      rintro z (⟨_, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ | ⟨_, -, rfl⟩) s' r' <;>
        exact ⟨by rintro ⟨_, _, -, -, ⟨⟩⟩, by rintro ⟨⟩⟩
    rcases h.hx with hx | hx | hx | hx | hx
    · obtain ⟨idx, x', hsend, hx'⟩ := xSend_sampled F K e auth s x hx tape
      refine ⟨.both s r, _, x', _, hsend, Or.inl rfl,
        h.hepoch, h.hauth, Or.inl hx', h.hy, h.hkem, ?_, ?_, ?_, h.htoX⟩
      · rintro s' r' hEq (hescr | hlag | hct2)
        · exact False.elim ((hnot_escr_lag x' (Or.inl hx') s' r').1 hescr)
        · exact False.elim ((hnot_escr_lag x' (Or.inl hx') s' r').2 hlag)
        · exact h.hcausal s' r' hEq (Or.inr (Or.inr hct2))
      · intro hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inl hx) s' r').2 hlag)
        · simp [noneMsg, hdrChunkMsg] at hmem
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact h.htoY m' hm'
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact Or.inr (Or.inl ⟨s, rfl, idx, rfl⟩)
    · obtain ⟨idx, x', hsend, hx'⟩ := xSend_hs F K e auth s r x hx tape
      refine ⟨.both s r, _, x', _, hsend, Or.inl rfl,
        h.hepoch, h.hauth, Or.inr (Or.inl hx'), h.hy, h.hkem, ?_, ?_, ?_, h.htoX⟩
      · rintro s' r' hEq (hescr | hlag | hct2)
        · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').1 hescr)
        · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').2 hlag)
        · exact h.hcausal s' r' hEq (Or.inr (Or.inr hct2))
      · intro hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inr (Or.inl hx)) s' r').2 hlag)
        · simp [noneMsg, chunkMsg] at hmem
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact h.htoY m' hm'
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact Or.inr (Or.inr (Or.inl ⟨s, r, rfl, Or.inl ⟨idx, rfl⟩⟩))
    · obtain ⟨idx, x', hsend, hx'⟩ := xSend_c1r F K e auth s r x hx tape
      refine ⟨.both s r, _, x', _, hsend, Or.inl rfl,
        h.hepoch, h.hauth, Or.inr (Or.inr (Or.inl hx')), h.hy, h.hkem, ?_, ?_, ?_, h.htoX⟩
      · rintro s' r' hEq (hescr | hlag | hct2)
        · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inr hx')) s' r').1 hescr)
        · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inr hx')) s' r').2 hlag)
        · exact h.hcausal s' r' hEq (Or.inr (Or.inr hct2))
      · intro hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inr (Or.inr hx)) s' r').2 hlag)
        · simp [noneMsg, chunkMsg] at hmem
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact h.htoY m' hm'
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact Or.inr (Or.inr (Or.inl ⟨s, r, rfl, Or.inr (Or.inl ⟨idx, rfl⟩)⟩))
    · refine ⟨.both s r, _, x, _, xSend_escr F K e auth s r x hx tape, Or.inl rfl,
        h.hepoch, h.hauth, Or.inr (Or.inr (Or.inr (Or.inl hx))), h.hy, h.hkem, h.hcausal, ?_, ?_, h.htoX⟩
      · intro hmem
        rcases List.mem_append.1 hmem with hmem | hmem
        · exact h.hlag hmem
        · simp [noneMsg, ackMsg] at hmem
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact h.htoY m' hm'
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact Or.inr (Or.inr (Or.inl ⟨s, r, rfl, Or.inr (Or.inr rfl)⟩))
    · refine ⟨.both s r, _, x, _, xSend_lag F K e auth s r x hx tape, Or.inl rfl,
        h.hepoch, h.hauth, Or.inr (Or.inr (Or.inr (Or.inr hx))), h.hy, h.hkem, h.hcausal, ?_, ?_, h.htoX⟩
      · intro _
        exact ⟨s, r, rfl, hx⟩
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · exact h.htoY m' hm'
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact Or.inr (Or.inr (Or.inr rfl))

/-- CT-side send preserves `InSyncE` on any coin tape of length `≥ 32` whose 32-byte prefix
satisfies `KemOk` when `c = .seed s`. -/
theorem inSyncE_sendY (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (tape : Bytes) (htape : 32 ≤ tape.length)
    (hkem : ∀ (s : Seed) (r : EncRand), c = .seed s → r.toList = tape.take 32 → KemOk K s r) :
    ∃ (c' : Coins) (m : Msg) (key : Option EpochSecret) (y' : St F) (tape' : Bytes),
      y.send K tape = .ok ({ msg := m, key := key, state := y' }, tape') ∧
      ((c' = c ∧ key = none) ∨
        ∃ s r, c = .seed s ∧ r.toList = tape.take 32 ∧ c' = .both s r ∧
          key = some { epoch := e, secret := secOf F K e s r }) ∧
      InSyncE F K e auth c' x y' toY (toX ++ [m]) := by
  have htoX_none : ∀ c, (∀ m ∈ toX, ToXOkE F K e auth c m) →
      ∀ m ∈ toX ++ [noneMsg e], ToXOkE F K e auth c m := by
    intro c htoX m hm
    rcases List.mem_append.1 hm with hm | hm
    · exact htoX m hm
    · rw [List.mem_singleton] at hm; exact Or.inr (Or.inl hm)
  cases c with
  | init =>
    have hnhr : ∀ s, y ≠ .headerReceived s := by obtain rfl := h.hy; rintro _ ⟨⟩
    exact ⟨.init, noneMsg e, none, y, tape, ySend_noHeader F K e auth none y h.hy hnhr tape,
      Or.inl ⟨rfl, rfl⟩, h.hepoch, h.hauth, h.hx, h.hy, h.hkem, by simp, h.hlag, h.htoY,
      htoX_none .init h.htoX⟩
  | seed s =>
    rcases hhy : h.hy with ⟨S, dec, hdec, hS, hy_eq⟩ | hy_eq
    · have hnhr : ∀ s', y ≠ .headerReceived s' := by subst hy_eq; rintro _ ⟨⟩
      exact ⟨.seed s, noneMsg e, none, y, tape, ySend_noHeader F K e auth (some s) y h.hy hnhr tape,
        Or.inl ⟨rfl, rfl⟩, h.hepoch, h.hauth, h.hx, h.hy, h.hkem, by simp, h.hlag, h.htoY,
        htoX_none (.seed s) h.htoX⟩
    · subst hy_eq
      have h32 : (tape.take 32).length = 32 := by simp; omega
      let r : EncRand := ⟨tape.take 32, h32⟩
      have hk : KemOk K s r := hkem s r rfl rfl
      obtain ⟨y', hsend, hy'⟩ := ySend_hr F K e auth s r hk tape rfl
      refine ⟨.both s r, chunkMsg .ct1 e (ct1Of K s r) 0#16,
        some { epoch := e, secret := secOf F K e s r }, y', tape.drop 32, hsend,
        Or.inr ⟨s, r, rfl, rfl, rfl, rfl⟩,
        h.hepoch, h.hauth, Or.inl h.hx, Or.inl hy', ?_, ?_, ?_, ?_, ?_⟩
      · rintro s' r' ⟨rfl, rfl⟩; exact hk
      · rintro s' r' ⟨rfl, rfl⟩ hcond
        exfalso
        obtain ⟨enc, -, hx_eq⟩ := h.hx
        rcases hcond with ⟨_, _, -, -, h1⟩ | h1 | ⟨idx, hmem⟩
        · cases hx_eq.symm.trans h1
        · cases hx_eq.symm.trans h1
        · rcases List.mem_append.1 hmem with hmem | hmem
          · rcases h.htoX _ hmem with hlt | heq | ⟨_, _, ⟨⟩, -⟩
            · exact BitVec.lt_irrefl e hlt
            · cases heq
          · simp [chunkMsg] at hmem
      · intro hmem; obtain ⟨_, _, ⟨⟩, -⟩ := h.hlag hmem
      · intro m' hm'
        rcases h.htoY m' hm' with hlt | ⟨s', hs', idx, rfl⟩ | ⟨_, _, ⟨⟩, -⟩ | rfl
        · exact Or.inl hlt
        · exact Or.inr (Or.inl ⟨s', hs', idx, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr rfl))
      · intro m' hm'
        rcases List.mem_append.1 hm' with hm' | hm'
        · rcases h.htoX m' hm' with hlt | rfl | ⟨_, _, ⟨⟩, -⟩
          · exact Or.inl hlt
          · exact Or.inr (Or.inl rfl)
        · rw [List.mem_singleton] at hm'
          exact Or.inr (Or.inr ⟨s, r, rfl, Or.inl ⟨0#16, hm'⟩⟩)
  | both s r =>
    have hk : KemOk K s r := h.hkem s r rfl
    have htoX_ct1 : ∀ idx, ∀ m ∈ toX ++ [chunkMsg .ct1 e (ct1Of K s r) idx],
        ToXOkE F K e auth (.both s r) m := by
      intro idx m hm
      rcases List.mem_append.1 hm with hm | hm
      · exact h.htoX m hm
      · rw [List.mem_singleton] at hm
        exact Or.inr (Or.inr ⟨s, r, rfl, Or.inl ⟨idx, hm⟩⟩)
    have hcausal_non_ct2 : ∀ m y', (∀ idx, chunkMsg .ct2 e (c2Msg F K e auth s r) idx ≠ m) →
        (YC2S F K e auth s r y → YC2S F K e auth s r y') →
        ∀ s' r', Coins.both s r = .both s' r' →
          (XESCR F K e auth s' r' x ∨ XLag F K e auth s' r' x ∨
            ∃ idx, chunkMsg .ct2 e (c2Msg F K e auth s' r') idx ∈ toX ++ [m]) →
          YC2S F K e auth s' r' y' := by
      rintro m y' hne_ct2 hy_imp s' r' ⟨rfl, rfl⟩ hcond
      apply hy_imp (h.hcausal s r rfl ?_)
      rcases hcond with h1 | h1 | ⟨idx, hmem⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · rcases List.mem_append.1 hmem with hmem | hmem
        · exact Or.inr (Or.inr ⟨idx, hmem⟩)
        · rw [List.mem_singleton] at hmem
          exact absurd hmem (hne_ct2 idx)
    rcases h.hy with hy | hy | hy | hy
    · obtain ⟨idx, y', hsend, hy'⟩ := ySend_c1s F K e auth s r y hy tape
      have hno : YC2S F K e auth s r y → YC2S F K e auth s r y' := by
        obtain ⟨_, _, _, -, -, -, rfl⟩ := hy; rintro ⟨_, -, ⟨⟩⟩
      exact ⟨.both s r, _, none, y', tape, hsend, Or.inl ⟨rfl, rfl⟩,
        h.hepoch, h.hauth, h.hx, Or.inl hy', h.hkem,
        hcausal_non_ct2 _ y' (by simp [chunkMsg]) hno, h.hlag, h.htoY, htoX_ct1 idx⟩
    · obtain ⟨idx, y', hsend, hy'⟩ := ySend_ekr F K e auth s r y hy tape
      have hno : YC2S F K e auth s r y → YC2S F K e auth s r y' := by
        obtain ⟨_, -, rfl⟩ := hy; rintro ⟨_, -, ⟨⟩⟩
      exact ⟨.both s r, _, none, y', tape, hsend, Or.inl ⟨rfl, rfl⟩,
        h.hepoch, h.hauth, h.hx, Or.inr (Or.inl hy'), h.hkem,
        hcausal_non_ct2 _ y' (by simp [chunkMsg]) hno, h.hlag, h.htoY, htoX_ct1 idx⟩
    · exact ⟨.both s r, noneMsg e, none, y, tape, ySend_c1a F K e auth s r y hy tape,
        Or.inl ⟨rfl, rfl⟩, h.hepoch, h.hauth, h.hx, Or.inr (Or.inr (Or.inl hy)), h.hkem,
        hcausal_non_ct2 _ y (by simp [chunkMsg, noneMsg]) id, h.hlag, h.htoY,
        htoX_none (.both s r) h.htoX⟩
    · obtain ⟨idx, y', hsend, hy'⟩ := ySend_c2s F K e auth s r hk y hy tape
      refine ⟨.both s r, _, none, y', tape, hsend, Or.inl ⟨rfl, rfl⟩,
        h.hepoch, h.hauth, h.hx, Or.inr (Or.inr (Or.inr hy')), h.hkem, ?_, h.hlag, h.htoY, ?_⟩
      · rintro s' r' ⟨rfl, rfl⟩ _; exact hy'
      · intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact h.htoX m hm
        · rw [List.mem_singleton] at hm
          exact Or.inr (Or.inr ⟨s, r, rfl, Or.inr ⟨idx, hm⟩⟩)

/-- EK-side receive of any `m ∈ toX` succeeds, outputs at most `(e, secOf F K e s r)`, and
preserves `InSyncE`. -/
theorem inSyncE_recvX (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (m : Msg) (hm : m ∈ toX) :
    ∃ (key : Option EpochSecret) (x' : St F), x.recv K m = .ok { key := key, state := x' } ∧
      (key = none ∨ ∃ s r, c = .both s r ∧ key = some { epoch := e, secret := secOf F K e s r }) ∧
      InSyncE F K e auth c x' y toY toX := by
  cases c with
  | init =>
    have hm1 : ToXOk e m := by
      rcases h.htoX m hm with hlt | rfl | ⟨_, _, ⟨⟩, -⟩
      · exact Or.inl hlt
      · exact Or.inr rfl
    exact ⟨none, x, xRecv F K e auth none x h.hx m hm1, Or.inl rfl, h⟩
  | seed s =>
    have hm1 : ToXOk e m := by
      rcases h.htoX m hm with hlt | rfl | ⟨_, _, ⟨⟩, -⟩
      · exact Or.inl hlt
      · exact Or.inr rfl
    exact ⟨none, x, xRecv F K e auth (some s) x h.hx m hm1, Or.inl rfl, h⟩
  | both s r =>
    have hk : KemOk K s r := h.hkem s r rfl
    have hnot_escr_lag : ∀ z : St F,
        (XShape F K e auth (some s) z ∨ XHS F K e auth s r z ∨ XC1R F K e auth s r z) →
        ∀ s' r', ¬ XESCR F K e auth s' r' z ∧ ¬ XLag F K e auth s' r' z := by
      rintro z (⟨_, -, rfl⟩ | ⟨_, _, _, -, -, -, rfl⟩ | ⟨_, -, rfl⟩) s' r' <;>
        exact ⟨by rintro ⟨_, _, -, -, ⟨⟩⟩, by rintro ⟨⟩⟩
    have hm_cases : m.epoch < e ∨ m = noneMsg e ∨
        (∃ idx, m = chunkMsg .ct1 e (ct1Of K s r) idx) ∨
        (∃ idx, m = chunkMsg .ct2 e (c2Msg F K e auth s r) idx) := by
      rcases h.htoX m hm with hlt | rfl | ⟨s', r', hEq, hch⟩
      · exact Or.inl hlt
      · exact Or.inr (Or.inl rfl)
      · cases hEq
        exact Or.inr (Or.inr hch)
    rcases h.hx with hx | hx | hx | hx | hx
    · rcases hm_cases with hlt | rfl | ⟨idx, rfl⟩ | ⟨idx, rfl⟩
      · exact ⟨none, x, xRecv_ks_ignore F K e auth s x hx m (Or.inl hlt), Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_ks_ignore F K e auth s x hx _ (Or.inr ⟨rfl, by simp [noneMsg]⟩),
          Or.inl rfl, h⟩
      · obtain ⟨x', hrecv, hx'⟩ := xRecv_ks_ct1 F K e auth s r hk x hx idx
        refine ⟨none, x', hrecv, Or.inl rfl,
          h.hepoch, h.hauth, Or.inr (Or.inl hx'), h.hy, h.hkem, ?_, ?_, h.htoY, h.htoX⟩
        · rintro s' r' hEq (hescr | hlag | hct2)
          · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').1 hescr)
          · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').2 hlag)
          · exact h.hcausal s' r' hEq (Or.inr (Or.inr hct2))
        · intro hmem
          obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inl hx) s' r').2 hlag)
      · exact ⟨none, x, xRecv_ks_ignore F K e auth s x hx _ (Or.inr ⟨rfl, by simp [chunkMsg]⟩),
          Or.inl rfl, h⟩
    · rcases hm_cases with hlt | rfl | ⟨idx, rfl⟩ | ⟨idx, rfl⟩
      · exact ⟨none, x, xRecv_hs_ignore F K e auth s r x hx m (Or.inl hlt), Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_hs_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [noneMsg]⟩),
          Or.inl rfl, h⟩
      · obtain ⟨x', hrecv, hx'⟩ := xRecv_hs_ct1 F K e auth s r hk x hx idx
        refine ⟨none, x', hrecv, Or.inl rfl,
          h.hepoch, h.hauth, ?_, h.hy, h.hkem, ?_, ?_, h.htoY, h.htoX⟩
        · rcases hx' with hx' | hx'
          · exact Or.inr (Or.inl hx')
          · exact Or.inr (Or.inr (Or.inl hx'))
        · rintro s' r' hEq (hescr | hlag | hct2)
          · rcases hx' with hx' | hx'
            · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').1 hescr)
            · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inr hx')) s' r').1 hescr)
          · rcases hx' with hx' | hx'
            · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inl hx')) s' r').2 hlag)
            · exact False.elim ((hnot_escr_lag x' (Or.inr (Or.inr hx')) s' r').2 hlag)
          · exact h.hcausal s' r' hEq (Or.inr (Or.inr hct2))
        · intro hmem
          obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inr (Or.inl hx)) s' r').2 hlag)
      · exact ⟨none, x, xRecv_hs_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [chunkMsg]⟩),
          Or.inl rfl, h⟩
    · rcases hm_cases with hlt | rfl | ⟨idx, rfl⟩ | ⟨idx, rfl⟩
      · exact ⟨none, x, xRecv_c1r_ignore F K e auth s r x hx m (Or.inl hlt), Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_c1r_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [noneMsg]⟩),
          Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_c1r_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [chunkMsg]⟩),
          Or.inl rfl, h⟩
      · obtain ⟨x', hrecv, hx'⟩ := xRecv_c1r_ct2 F K e auth s r hk x hx idx
        refine ⟨none, x', hrecv, Or.inl rfl,
          h.hepoch, h.hauth, Or.inr (Or.inr (Or.inr (Or.inl hx'))), h.hy, h.hkem, ?_, ?_, h.htoY, h.htoX⟩
        · rintro s' r' hEq _
          cases hEq
          exact h.hcausal s r rfl (Or.inr (Or.inr ⟨idx, hm⟩))
        · intro hmem
          obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
          exact False.elim ((hnot_escr_lag x (Or.inr (Or.inr hx)) s' r').2 hlag)
    · rcases hm_cases with hlt | rfl | ⟨idx, rfl⟩ | ⟨idx, rfl⟩
      · exact ⟨none, x, xRecv_escr_ignore F K e auth s r x hx m (Or.inl hlt), Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_escr_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [noneMsg]⟩),
          Or.inl rfl, h⟩
      · exact ⟨none, x, xRecv_escr_ignore F K e auth s r x hx _ (Or.inr ⟨rfl, by simp [chunkMsg]⟩),
          Or.inl rfl, h⟩
      · have hy_c2s : YC2S F K e auth s r y := h.hcausal s r rfl (Or.inl hx)
        have hnot_lag_x : ∀ s' r', ¬ XLag F K e auth s' r' x := by
          obtain ⟨_, _, -, -, rfl⟩ := hx
          rintro _ _ ⟨⟩
        obtain ⟨x', ⟨hrecv, hx'⟩ | ⟨hrecv, hx'⟩⟩ := xRecv_escr_ct2 F K e auth s r hk h.hepoch x hx idx
        · refine ⟨none, x', hrecv, Or.inl rfl,
            h.hepoch, h.hauth, Or.inr (Or.inr (Or.inr (Or.inl hx'))), h.hy, h.hkem, ?_, ?_, h.htoY, h.htoX⟩
          · rintro s' r' hEq _
            cases hEq
            exact hy_c2s
          · intro hmem
            obtain ⟨s', r', _, hlag⟩ := h.hlag hmem
            exact False.elim (hnot_lag_x s' r' hlag)
        · refine ⟨some { epoch := e, secret := secOf F K e s r }, x', hrecv,
            Or.inr ⟨s, r, rfl, rfl⟩,
            h.hepoch, h.hauth, Or.inr (Or.inr (Or.inr (Or.inr hx'))), h.hy, h.hkem, ?_, ?_, h.htoY, h.htoX⟩
          · rintro s' r' hEq _
            cases hEq
            exact hy_c2s
          · intro _
            exact ⟨s, r, rfl, hx'⟩
    · have hm_le : m.epoch ≤ e := by
        rcases hm_cases with hlt | rfl | ⟨idx, rfl⟩ | ⟨idx, rfl⟩
        · exact BitVec.le_of_lt hlt
        all_goals exact BitVec.le_refl e
      exact ⟨none, x, xRecv_lag F K e auth s r h.hepoch x hx m hm_le, Or.inl rfl, h⟩

/-- CT-side receive of any `m ∈ toY` other than `noneMsg (e + 1)` succeeds without key output
and preserves `InSyncE`. -/
theorem inSyncE_recvY (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (m : Msg) (hm : m ∈ toY) (hne : m ≠ noneMsg (e + 1#64)) :
    ∃ y' : St F, y.recv K m = .ok { key := none, state := y' } ∧
      InSyncE F K e auth c x y' toY toX := by
  have hm_ok := h.htoY m hm
  cases c with
  | init =>
    have hm1 : ToYOk F K e auth none m := by
      rcases hm_ok with hlt | ⟨_, ⟨⟩, -⟩ | ⟨_, _, ⟨⟩, -⟩ | heq
      · exact Or.inl hlt
      · exact absurd heq hne
    obtain ⟨y', hrecv, hy'⟩ := yRecv F K e auth h.hauth none y h.hy m hm1
    exact ⟨y', hrecv, { h with hy := hy', hcausal := by simp }⟩
  | seed s =>
    have hm1 : ToYOk F K e auth (some s) m := by
      rcases hm_ok with hlt | ⟨s', hs', idx, rfl⟩ | ⟨_, _, ⟨⟩, -⟩ | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨s', hs', idx, rfl⟩
      · exact absurd heq hne
    obtain ⟨y', hrecv, hy'⟩ := yRecv F K e auth h.hauth (some s) y h.hy m hm1
    exact ⟨y', hrecv, { h with hy := hy', hcausal := by simp }⟩
  | both s r =>
    have hk : KemOk K s r := h.hkem s r rfl
    have hfinish : ∀ y', y.recv K m = .ok { key := none, state := y' } →
        YShapeE F K e auth (.both s r) y' →
        (YC2S F K e auth s r y → YC2S F K e auth s r y') →
        ∃ y', y.recv K m = .ok { key := none, state := y' } ∧
          InSyncE F K e auth (.both s r) x y' toY toX := by
      intro y' hrecv hy' himp
      refine ⟨y', hrecv, { h with hy := hy', hcausal := ?_ }⟩
      rintro s' r' ⟨rfl, rfl⟩ hcond
      exact himp (h.hcausal s r rfl hcond)
    rcases h.hy with hy | hy | hy | hy
    · have hno : ∀ {y'}, YC2S F K e auth s r y → YC2S F K e auth s r y' := by
        obtain ⟨_, _, _, -, -, -, rfl⟩ := hy; rintro _ ⟨_, -, ⟨⟩⟩
      rcases hm_ok with hlt | ⟨s', ⟨rfl⟩, idx, rfl⟩ |
          ⟨s', r', ⟨rfl, rfl⟩, ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl⟩ | heq
      · exact hfinish y (yRecv_c1s_ignore F K e auth s r y hy m (Or.inl hlt)) (Or.inl hy) hno
      · exact hfinish y (yRecv_c1s_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [hdrChunkMsg], by simp [hdrChunkMsg]⟩)) (Or.inl hy) hno
      · obtain ⟨y', hrecv, hy' | hy'⟩ := yRecv_c1s_ek F K e auth s r hk y hy idx
        · exact hfinish y' hrecv (Or.inl hy') hno
        · exact hfinish y' hrecv (Or.inr (Or.inl hy')) hno
      · obtain ⟨y', hrecv, hy' | hy'⟩ := yRecv_c1s_ekAck F K e auth s r hk y hy idx
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inl hy'))) hno
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inr hy'))) hno
      · exact hfinish y (yRecv_c1s_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [ackMsg], by simp [ackMsg]⟩)) (Or.inl hy) hno
      · exact absurd heq hne
    · have hno : ∀ {y'}, YC2S F K e auth s r y → YC2S F K e auth s r y' := by
        obtain ⟨_, -, rfl⟩ := hy; rintro _ ⟨_, -, ⟨⟩⟩
      rcases hm_ok with hlt | ⟨s', ⟨rfl⟩, idx, rfl⟩ |
          ⟨s', r', ⟨rfl, rfl⟩, ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl⟩ | heq
      · exact hfinish y (yRecv_ekr_ignore F K e auth s r y hy m (Or.inl hlt))
          (Or.inr (Or.inl hy)) hno
      · exact hfinish y (yRecv_ekr_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [hdrChunkMsg], by simp [hdrChunkMsg]⟩)) (Or.inr (Or.inl hy)) hno
      · exact hfinish y (yRecv_ekr_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [chunkMsg], by simp [chunkMsg]⟩)) (Or.inr (Or.inl hy)) hno
      · obtain ⟨y', hrecv, hy'⟩ := yRecv_ekr_ack F K e auth s r hk y hy _ (Or.inr ⟨idx, rfl⟩)
        exact hfinish y' hrecv (Or.inr (Or.inr (Or.inr hy'))) hno
      · obtain ⟨y', hrecv, hy'⟩ := yRecv_ekr_ack F K e auth s r hk y hy _ (Or.inl rfl)
        exact hfinish y' hrecv (Or.inr (Or.inr (Or.inr hy'))) hno
      · exact absurd heq hne
    · have hno : ∀ {y'}, YC2S F K e auth s r y → YC2S F K e auth s r y' := by
        obtain ⟨_, _, -, -, rfl⟩ := hy; rintro _ ⟨_, -, ⟨⟩⟩
      rcases hm_ok with hlt | ⟨s', ⟨rfl⟩, idx, rfl⟩ |
          ⟨s', r', ⟨rfl, rfl⟩, ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl⟩ | heq
      · exact hfinish y (yRecv_c1a_ignore F K e auth s r y hy m (Or.inl hlt))
          (Or.inr (Or.inr (Or.inl hy))) hno
      · exact hfinish y (yRecv_c1a_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [hdrChunkMsg], by simp [hdrChunkMsg]⟩))
          (Or.inr (Or.inr (Or.inl hy))) hno
      · obtain ⟨y', hrecv, hy' | hy'⟩ :=
          yRecv_c1a_ek F K e auth s r hk y hy MessagePayload.ek (Or.inl rfl) idx
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inl hy'))) hno
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inr hy'))) hno
      · obtain ⟨y', hrecv, hy' | hy'⟩ :=
          yRecv_c1a_ek F K e auth s r hk y hy MessagePayload.ekCt1Ack (Or.inr rfl) idx
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inl hy'))) hno
        · exact hfinish y' hrecv (Or.inr (Or.inr (Or.inr hy'))) hno
      · exact hfinish y (yRecv_c1a_ignore F K e auth s r y hy _
          (Or.inr ⟨rfl, by simp [ackMsg], by simp [ackMsg]⟩))
          (Or.inr (Or.inr (Or.inl hy))) hno
      · exact absurd heq hne
    · have hle : m.epoch ≤ e := by
        rcases hm_ok with hlt | ⟨_, _, idx, rfl⟩ |
            ⟨_, _, -, ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl⟩ | heq
        · exact BitVec.le_of_lt hlt
        · exact BitVec.le_refl e
        · exact BitVec.le_refl e
        · exact BitVec.le_refl e
        · exact BitVec.le_refl e
        · exact absurd heq hne
      exact hfinish y (yRecv_c2s_old F K e auth s r y hy m hle) (Or.inr (Or.inr (Or.inr hy))) id

/-- Inter-epoch role swap: when `Y_e` receives `noneMsg (e + 1)` and `e.toNat + 2 < 2 ^ 64`,
`Y_e` becomes `X_{e+1}` (`.keysUnsampled`) and `X_e` (`XLag`) becomes `Y_{e+1}`, establishing
`InSyncE` at `e + 1` with `authNext` and `.init` coins. -/
theorem inSyncE_next (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX)
    (hm : noneMsg (e + 1#64) ∈ toY) (hnext : e.toNat + 2 < 2 ^ 64) :
    ∃ s r, c = .both s r ∧ ∃ x' : St F,
      y.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := x' } ∧
      InSyncE F K (e + 1#64) (authNext F K e auth s r) .init x' x toX toY := by
  obtain ⟨s, r, rfl, hlag⟩ := h.hlag hm
  have hy := h.hcausal s r rfl (Or.inr (Or.inl hlag))
  refine ⟨s, r, rfl, _, yRecv_c2s_next F K e auth s r h.hepoch y hy, ?_⟩
  have he1 : (e + 1#64).toNat = e.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  have he2 : (e + 1#64 + 1#64).toNat = e.toNat + 2 := by rw [BitVec.toNat_add, he1]; simp; omega
  have hlt : ∀ m : Msg, m.epoch ≤ e → m.epoch < e + 1#64 := by
    intro m hm; simp only [BitVec.lt_def, BitVec.le_def, he1] at hm ⊢; omega
  refine ⟨by rw [he1]; omega, authWf_update _ _ _ _, rfl, hlag, by simp, by simp, ?_, ?_, ?_⟩
  · intro hmem
    exfalso
    rcases h.htoX _ hmem with hl | heq | ⟨s', r', -, ⟨idx, heq⟩ | ⟨idx, heq⟩⟩
    · simp only [noneMsg, BitVec.lt_def, he2] at hl; omega
    · have h' := congrArg (fun m : Msg => m.epoch.toNat) heq
      simp only [noneMsg, he2] at h'; omega
    · simp [noneMsg, chunkMsg] at heq
    · simp [noneMsg, chunkMsg] at heq
  · intro m hmem
    left
    apply hlt
    rcases h.htoX m hmem with hl | rfl | ⟨_, _, -, ⟨idx, rfl⟩ | ⟨idx, rfl⟩⟩
    · simp only [BitVec.lt_def, BitVec.le_def] at hl ⊢; omega
    all_goals exact BitVec.le_refl e
  · intro m hmem
    rcases h.htoY m hmem with hl | ⟨_, -, idx, rfl⟩ | ⟨_, _, -, ⟨idx, rfl⟩ | ⟨idx, rfl⟩ | rfl⟩ | rfl
    · exact Or.inl (hlt m (by simp only [BitVec.lt_def, BitVec.le_def] at hl ⊢; omega))
    all_goals first
      | exact Or.inr (Or.inl rfl)
      | exact Or.inl (hlt _ (BitVec.le_refl e))

/-- Both states in `InSyncE` round-trip through `States.from_pb ∘ States.into_pb`. -/
theorem inSyncE_codec (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth c x y toY toX) :
    States.from_pb spqrPolyApi (spqrAuthApi F) x.into_pb = .ok x ∧
      States.from_pb spqrPolyApi (spqrAuthApi F) y.into_pb = .ok y :=
  ⟨xShapeE_codec F K e auth c h.hkem x h.hx, yShapeE_codec F K e auth c h.hkem y h.hy⟩

/-! ## Party-level orientation -/

/-- `ekSide` alternates parity between `e` and `e + 1` when `e.toNat + 1 < 2 ^ 64`. -/
theorem ekSide_succ (e : Epoch) (he : e.toNat + 1 < 2 ^ 64) : ekSide (e + 1#64) ≠ ekSide e := by
  have he1 : (e + 1#64).toNat = e.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
  unfold ekSide
  rw [he1]
  split_ifs <;> first | omega | simp

/-- `States.init_a` and `States.init_b` satisfy two-party `InSync` at epoch `1`. -/
theorem inSync_init (F : ShaCompress) (K : MlKem) (authKey : Bytes) :
    ∃ stA stB : St F, States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok stA ∧
      States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok stB ∧
      InSync F K 1#64 (Authenticator.new F authKey 1#64) .init stA stB [] [] := by
  obtain ⟨x, y, hx, hy, h⟩ := inSyncE_init F K authKey
  exact ⟨x, y, hx, hy, h⟩

end CryptoVerification.SpqrV1Sync.Braid
