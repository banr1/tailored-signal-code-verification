/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostNone
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Helpers for `SegPostSome`

Instruction decode lemmas, pure model bridges, and stack/record spatial decompositions for
`segPostSome_ok`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Instruction decode lemmas for `SegPostSome` (`0x3c3f8:31`, `0x3c55c:8`, `0x3ca08:6`) -/

gen_decodes libsignalSessionCode_tree messageDecryptPostSomeBin [(ls_off% "session_message_decrypt_signal" + 8016) → (ls_off% "session_message_decrypt_signal" + 8092), raw (ls_off% "session_message_decrypt_signal" + 8096),
    (ls_off% "session_message_decrypt_signal" + 8100) → (ls_off% "session_message_decrypt_signal" + 8136), (ls_off% "session_message_decrypt_signal" + 8372) → (ls_off% "session_message_decrypt_signal" + 8400), (ls_off% "session_message_decrypt_signal" + 9568) → (ls_off% "session_message_decrypt_signal" + 9588)]

/-! ## 2. Pure Session-API Model and `RecordDecryptGhost` Model Lemmas -/

theorem draws_eq_region_draws (C : Crypto) (x : DecryptGhost) (prevPtr : BitVec 64)
    (G : SessionGhost) (ses : Session (List (BitVec 8)))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rec_ : SessionRecord (List (BitVec 8)))
    (hLoad : ans.loadSession = .ok (some rec_)) (hCur : rec_.currentSession = some ses) :
    x.draws C ans = (recGhostOf x prevPtr G ses.state).draws C := by
  unfold DecryptGhost.draws loadedSession RecordDecryptGhost.draws recGhostOf
  simp only [hLoad, hCur]

theorem serializeAddrVals_eq_serializeAddresses (parse : ServiceIdParser) (rem loc : AddrGhost) :
    serializeAddrVals parse rem.val loc.val = serializeAddresses parse rem loc := rfl

theorem model_of_region_err (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (prevPtr : BitVec 64) (G : SessionGhost) (ses : Session (List (BitVec 8)))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rec_ : SessionRecord (List (BitVec 8)))
    (e : SignalProtocolError)
    (hLoad : ans.loadSession = .ok (some rec_)) (hCur : rec_.currentSession = some ses)
    (hErr : ((recGhostOf x prevPtr G ses.state).model C S uuidTryParse).1 = .error e)
    (hnp : e ≠ .panic) :
    x.model C S uuidTryParse ans = (.error (.protocol e), [.loadSession x.rem.val]) := by
  rw [DecryptGhost.model, messageDecryptSignal_eq_flat]
  simp only [decryptFlat, hLoad, SessionRecord.tryDecryptFromRecord, hCur,
    serializeAddrVals_eq_serializeAddresses]
  simp only [RecordDecryptGhost.model, recGhostOf] at hErr
  rcases hTry : SessionState.tryDecryptFromRecord C S.spqr
      (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc) x.msg .whisper
      (coinsOf x.rest) ses.state with ⟨r, st'⟩
  rw [hTry] at hErr
  subst hErr
  cases e <;> simp_all [ApiError.ofProtocol]

theorem decryptRecord_of_region_ok (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (prevPtr : BitVec 64) (G : SessionGhost) (ses : Session (List (BitVec 8)))
    (rec_ : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (st' : SessionState (List (BitVec 8)))
    (hCur : rec_.currentSession = some ses)
    (hOk : (recGhostOf x prevPtr G ses.state).model C S uuidTryParse = (.ok pt, st')) :
    decryptRecord C S uuidTryParse x rec_ =
      .ok (pt, ⟨some { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }⟩) := by
  simp only [decryptRecord, SessionRecord.tryDecryptFromRecord, hCur,
    serializeAddrVals_eq_serializeAddresses]
  simp only [RecordDecryptGhost.model, recGhostOf] at hOk
  rw [hOk]

theorem model_panic_of_remoteIdentity_none (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (prevPtr : BitVec 64) (G : SessionGhost) (ses : Session (List (BitVec 8)))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (rec_ : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (st' : SessionState (List (BitVec 8)))
    (hLoad : ans.loadSession = .ok (some rec_)) (hCur : rec_.currentSession = some ses)
    (hOk : (recGhostOf x prevPtr G ses.state).model C S uuidTryParse = (.ok pt, st'))
    (hNone : st'.remoteIdentity = none) :
    (x.model C S uuidTryParse ans).1 = .error .panic := by
  rw [DecryptGhost.model, messageDecryptSignal_eq_flat]
  have hDec := decryptRecord_of_region_ok C S x prevPtr G ses rec_ pt st' hCur hOk
  simp only [decryptRecord] at hDec
  simp only [decryptFlat, hLoad, hDec, Option.bind, hNone]

theorem speWord_add_two_ne_zero (i : Nat) (hi : i < 2 ^ 63 - 2) :
    speWord i + 2#64 ≠ 0#64 := by
  unfold speWord
  bv_omega

theorem recordResultTag_err_add_two_ne_zero (e : SignalProtocolError) (hnp : e ≠ .panic) :
    recordResultTag (.error e) + 2#64 ≠ 0#64 := by
  cases e with
  | invalidState => exact speWord_add_two_ne_zero 1 (by omega)
  | ciphertextMessageTooShort _ => exact speWord_add_two_ne_zero 3 (by omega)
  | legacyCiphertextVersion _ => exact speWord_add_two_ne_zero 4 (by omega)
  | unrecognizedCiphertextVersion _ => exact speWord_add_two_ne_zero 5 (by omega)
  | invalidProtobufEncoding => exact speWord_add_two_ne_zero 2 (by omega)
  | noKeyTypeIdentifier => exact speWord_add_two_ne_zero 7 (by omega)
  | badKeyType _ => exact speWord_add_two_ne_zero 8 (by omega)
  | badKeyLength _ => exact speWord_add_two_ne_zero 9 (by omega)
  | invalidKeyAgreement => exact speWord_add_two_ne_zero 10 (by omega)
  | invalidSessionStructure _ => exact speWord_add_two_ne_zero 20 (by omega)
  | duplicatedMessage _ _ => exact speWord_add_two_ne_zero 23 (by omega)
  | invalidMessage _ _ => exact speWord_add_two_ne_zero 24 (by omega)
  | panic => exact False.elim (hnp rfl)

theorem speWord_ne_pendingTag (i : Nat) (hi : i < 2 ^ 63 - 3) :
    speWord i ≠ pendingTag := by
  unfold speWord pendingTag
  bv_omega

theorem recordResultTag_err_ne_pendingTag (e : SignalProtocolError) (hnp : e ≠ .panic) :
    recordResultTag (.error e) ≠ pendingTag := by
  cases e with
  | invalidState => exact speWord_ne_pendingTag 1 (by omega)
  | ciphertextMessageTooShort _ => exact speWord_ne_pendingTag 3 (by omega)
  | legacyCiphertextVersion _ => exact speWord_ne_pendingTag 4 (by omega)
  | unrecognizedCiphertextVersion _ => exact speWord_ne_pendingTag 5 (by omega)
  | invalidProtobufEncoding => exact speWord_ne_pendingTag 2 (by omega)
  | noKeyTypeIdentifier => exact speWord_ne_pendingTag 7 (by omega)
  | badKeyType _ => exact speWord_ne_pendingTag 8 (by omega)
  | badKeyLength _ => exact speWord_ne_pendingTag 9 (by omega)
  | invalidKeyAgreement => exact speWord_ne_pendingTag 10 (by omega)
  | invalidSessionStructure _ => exact speWord_ne_pendingTag 20 (by omega)
  | duplicatedMessage _ _ => exact speWord_ne_pendingTag 23 (by omega)
  | invalidMessage _ _ => exact speWord_ne_pendingTag 24 (by omega)
  | panic => exact False.elim (hnp rfl)

/-! ## 3. 40-Byte Inline Decomposition for `recordResultAt A a (.error e)` -/

abbrev vecU8Buf := Pf.SegPostNone.vecU8Buf

theorem vecU8_eq_bytes24_sep_buf (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦ₛ (unpack64 cap ++ unpack64 ptr ++ unpack64 (BitVec.ofNat 64 bs.length))) ∗
        vecU8Buf A cap ptr bs := by
  rw [vecU8_eq_exists_buf A a bs]
  congr 1; funext cap; congr 1; funext ptr
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append,
      unpack64_length, unpack64_length, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem strRefAt_eq_bytes16_sep_ro (a : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt a lit =
      ∃∗ p : BitVec 64,
        (a ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 lit.length))) ∗ (p ↦ᵣ lit) := by
  unfold strRefAt
  congr 1; funext p
  rw [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, sepConj_assoc]

private theorem speAt_tag_region40 (w0 : BitVec 64) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ memRegion (a + 8#64) 40) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
          (b ↦₆₄ w0) ∗ memRegion (b + 8#64) 40⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [memRegion_eq_exists_bytes (a + 8#64) 40 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  have h1 : (a ↦₆₄ w0) ∗ (⌜bs.length = 40⌝ ∗ ((a + 8#64) ↦ₛ bs)) =
      ⌜bs.length = 40⌝ ∗ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; intro hbs
  refine Entails.sepExists_right bs (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨hbs, fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp]
  exact sepConj_mono_right (hbs ▸ pointsToBytes_entails_memRegion (b + 8#64) bs)

private theorem speAt_tag_word_region32 (w0 w1 : BitVec 64) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ memRegion (a + 16#64) 32) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
          (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₆₄ w1) ∗ memRegion (b + 16#64) 32⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [pointsTo64_eq_pointsToBytes (a + 8#64),
      memRegion_eq_exists_bytes (a + 16#64) 32 (by decide),
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  have ha16 : ∀ c : BitVec 64, c + 8#64 + BitVec.ofNat 64 (unpack64 w1).length = c + 16#64 := by
    intro c; change c + 8#64 + 8#64 = c + 16#64; bv_omega
  have h1 : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ unpack64 w1) ∗ (⌜tail.length = 32⌝ ∗ ((a + 16#64) ↦ₛ tail)) =
      ⌜tail.length = 32⌝ ∗ (a ↦₆₄ w0) ∗ (((a + 8#64) ↦ₛ unpack64 w1) ∗ ((a + 16#64) ↦ₛ tail)) := by ac_rfl
  rw [h1]
  apply Entails.pure_left; intro htail
  refine Entails.sepExists_right (unpack64 w1 ++ tail) (Entails.sepExists_right emp ?_)
  rw [pointsToBytes_append, ha16 a, sepConj_emp]
  refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (Entails.refl _)
  simp only [pointsToBytes_append, ha16 b, ← pointsTo64_eq_pointsToBytes, sepConj_emp]
  exact sepConj_mono_right (sepConj_mono_right (htail ▸ pointsToBytes_entails_memRegion (b + 16#64) tail))

private theorem speAt_tag_byte_region39 (w0 : BitVec 64) (v : BitVec 8) (a : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ v) ∗ memRegion (a + 9#64) 39) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64, ((b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
          (b ↦₆₄ w0) ∗ ((b + 8#64) ↦₈ v) ∗ memRegion (b + 9#64) 39⌝ ∗
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  rw [memRegion_eq_exists_bytes (a + 9#64) 39 (by decide),
      sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  have hcons : ∀ d : BitVec 64, ((d + 8#64) ↦₈ v) ∗ ((d + 9#64) ↦ₛ tail) = ((d + 8#64) ↦ₛ (v :: tail)) := by
    intro d
    have hd9 : d + 9#64 = d + 8#64 + 1#64 := by bv_omega
    rw [hd9, ← pointsToBytes_cons]
  have h1 : (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₈ v) ∗ (⌜tail.length = 39⌝ ∗ ((a + 9#64) ↦ₛ tail)) =
      ⌜tail.length = 39⌝ ∗ (a ↦₆₄ w0) ∗ (((a + 8#64) ↦₈ v) ∗ ((a + 9#64) ↦ₛ tail)) := by ac_rfl
  rw [h1, hcons a]
  apply Entails.pure_left; intro htail
  refine Entails.sepExists_right (v :: tail) (Entails.sepExists_right emp ?_)
  rw [sepConj_emp]
  refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (Entails.refl _)
  simp only [← hcons b, sepConj_emp]
  exact sepConj_mono_right (sepConj_mono_right (htail ▸ pointsToBytes_entails_memRegion (b + 9#64) tail))

theorem recordResultAt_err_inline_40 (A : RustAlloc) (a : BitVec 64)
    (e : SignalProtocolError) (hne : e ≠ .panic) :
    recordResultAt A a (.error e) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 40 ∧ ∀ b : BitVec 64,
          ((b ↦₆₄ recordResultTag (.error e)) ∗ ((b + 8#64) ↦ₛ bs) ∗ H) ⊢
            recordResultAt A b (.error e)⌝ ∗
        (a ↦₆₄ recordResultTag (.error e)) ∗ ((a + 8#64) ↦ₛ bs) ∗ H := by
  cases e with
  | panic => exact absurd rfl hne
  | invalidProtobufEncoding | noKeyTypeIdentifier | invalidKeyAgreement =>
    exact speAt_tag_region40 _ a
  | ciphertextMessageTooShort n | badKeyLength n =>
    exact speAt_tag_word_region32 _ _ a
  | duplicatedMessage i c =>
    dsimp only [recordResultAt, vecResultAt, speAt, recordResultTag]
    have hp : ∀ d : BitVec 64,
        ((d ↦₆₄ speWord 23) ∗ ((d + 8#64) ↦₃₂ i) ∗ ((d + 12#64) ↦₃₂ c) ∗ memRegion (d + 16#64) 32) =
        ((d ↦₆₄ speWord 23) ∗ ((d + 8#64) ↦₆₄ (c ++ i)) ∗ memRegion (d + 16#64) 32) := by
      intro d
      have hd12 : d + 12#64 = d + 8#64 + 4#64 := by bv_omega
      rw [← sepConj_assoc ((d + 8#64) ↦₃₂ i), hd12, pointsTo32_pair]
    rw [hp a]
    simpa only [hp] using speAt_tag_word_region32 (speWord 23) (c ++ i) a
  | legacyCiphertextVersion v | unrecognizedCiphertextVersion v | badKeyType v =>
    exact speAt_tag_byte_region39 _ v a
  | invalidSessionStructure r =>
    dsimp only [recordResultAt, vecResultAt, speAt, recordResultTag]
    rw [strRefAt_eq_bytes16_sep_ro (a + 8#64) (invalidSessionStructureStr r),
        memRegion_eq_exists_bytes (a + 24#64) 24 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro p
    have ha24 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)).length = d + 24#64 := by
      intro d; change d + 8#64 + 16#64 = d + 24#64; bv_omega
    have h1 :
        (a ↦₆₄ speWord 20) ∗
          (((a + 8#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length))) ∗ (p ↦ᵣ invalidSessionStructureStr r)) ∗
          (⌜tail.length = 24⌝ ∗ ((a + 24#64) ↦ₛ tail)) =
        ⌜tail.length = 24⌝ ∗ (a ↦₆₄ speWord 20) ∗
          (((a + 8#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length))) ∗ ((a + 24#64) ↦ₛ tail)) ∗
          (p ↦ᵣ invalidSessionStructureStr r) := by ac_rfl
    rw [h1]
    apply Entails.pure_left; intro htail
    refine Entails.sepExists_right (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length) ++ tail)
      (Entails.sepExists_right (p ↦ᵣ invalidSessionStructureStr r) ?_)
    rw [pointsToBytes_append (a + 8#64) (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)) tail, ha24 a]
    refine Entails.pure_right ⟨by simp [htail], fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_append (b + 8#64) (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length)) tail,
        ha24 b, strRefAt_eq_bytes16_sep_ro (b + 8#64) (invalidSessionStructureStr r)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right p ?_
    have hgoal :
        ((b ↦₆₄ speWord 20) ∗
          (((b + 8#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length))) ∗
            ((b + 24#64) ↦ₛ tail)) ∗ (p ↦ᵣ invalidSessionStructureStr r)) =
        ((b ↦₆₄ speWord 20) ∗
          (((b + 8#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (invalidSessionStructureStr r).length))) ∗
            (p ↦ᵣ invalidSessionStructureStr r)) ∗ ((b + 24#64) ↦ₛ tail)) := by ac_rfl
    rw [hgoal]
    exact sepConj_mono_right (sepConj_mono_right (htail ▸ pointsToBytes_entails_memRegion (b + 24#64) tail))
  | invalidState =>
    dsimp only [recordResultAt, vecResultAt, speAt, recordResultTag]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [vecU8_eq_bytes24_sep_buf A (a + 8#64) bs,
        strRefAt_eq_bytes16_sep_ro (a + 32#64) (utf8 "decrypt")]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro p
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    let vh := unpack64 cap ++ unpack64 ptr ++ unpack64 (BitVec.ofNat 64 bs.length)
    have ha32 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 vh.length = d + 32#64 := by
      intro d; change d + 8#64 + 24#64 = d + 32#64; bv_omega
    refine Entails.sepExists_right
      (vh ++ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length)))
      (Entails.sepExists_right (vecU8Buf A cap ptr bs ∗ (p ↦ᵣ utf8 "decrypt")) ?_)
    have h1 :
        (a ↦₆₄ speWord 1) ∗
          (((a + 8#64) ↦ₛ vh) ∗ vecU8Buf A cap ptr bs) ∗
          (((a + 32#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length))) ∗ (p ↦ᵣ utf8 "decrypt")) =
        (a ↦₆₄ speWord 1) ∗
          (((a + 8#64) ↦ₛ vh) ∗
            ((a + 32#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length)))) ∗
          (vecU8Buf A cap ptr bs ∗ (p ↦ᵣ utf8 "decrypt")) := by ac_rfl
    rw [h1,
        pointsToBytes_append (a + 8#64) vh
          (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length)),
        ha32 a]
    refine Entails.pure_right ⟨by simp [vh], fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_append (b + 8#64) vh
          (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length)),
        ha32 b]
    refine Entails.sepExists_right bs ?_
    rw [vecU8_eq_bytes24_sep_buf A (b + 8#64) bs,
        strRefAt_eq_bytes16_sep_ro (b + 32#64) (utf8 "decrypt")]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_right p (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_))
    have hb :
        (b ↦₆₄ speWord 1) ∗
          (((b + 8#64) ↦ₛ vh) ∗
            ((b + 32#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length)))) ∗
          (vecU8Buf A cap ptr bs ∗ (p ↦ᵣ utf8 "decrypt")) =
        (b ↦₆₄ speWord 1) ∗
          (((b + 8#64) ↦ₛ vh) ∗ vecU8Buf A cap ptr bs) ∗
          (((b + 32#64) ↦ₛ (unpack64 p ++ unpack64 (BitVec.ofNat 64 (utf8 "decrypt").length))) ∗ (p ↦ᵣ utf8 "decrypt")) := by ac_rfl
    rw [hb]
    exact Entails.refl _
  | invalidMessage t r =>
    let strAt (d : BitVec 64) : SepProp :=
      match r with
      | .decryptionFailed => vecU8 A d decryptionFailedStr
      | _ => invalidMessageStrAt A d r
    have hrec_eq : ∀ d : BitVec 64,
        recordResultAt A d (.error (.invalidMessage t r)) =
          (d ↦₆₄ speWord 24) ∗ strAt (d + 8#64) ∗ ((d + 32#64) ↦₈ msgTypeByte t) ∗
            memRegion (d + 33#64) 15 := by
      intro d; cases r <;> rfl
    have htag : recordResultTag (.error (.invalidMessage t r)) = speWord 24 := rfl
    rw [hrec_eq a, htag]
    have hstr : ∀ d : BitVec 64,
        strAt d ⊢
          ∃∗ bs : List (BitVec 8),
            ⌜∀ c : BitVec 64, vecU8 A c bs ⊢ strAt c⌝ ∗ vecU8 A d bs := by
      intro d
      cases r with
      | tooFarInFuture =>
        exact Entails.sepExists_right tooFarInFutureStr
          (Entails.pure_right (fun _ => Entails.refl _) (Entails.refl _))
      | macFailed =>
        exact Entails.sepExists_right macFailedStr
          (Entails.pure_right (fun _ => Entails.refl _) (Entails.refl _))
      | pqRatchet =>
        apply Entails.sepExists_elim; intro bs
        exact Entails.sepExists_right bs
          (Entails.pure_right (fun c => Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _))
      | badCiphertext =>
        apply Entails.sepExists_elim; intro bs
        exact Entails.sepExists_right bs
          (Entails.pure_right (fun c => Entails.sepExists_right bs (Entails.refl _)) (Entails.refl _))
      | decryptionFailed =>
        exact Entails.sepExists_right decryptionFailedStr
          (Entails.pure_right (fun _ => Entails.refl _) (Entails.refl _))
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left (hstr (a + 8#64)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [vecU8_eq_bytes24_sep_buf A (a + 8#64) bs,
        memRegion_eq_exists_bytes (a + 33#64) 15 (by decide)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro tail
    apply Entails.sepExists_elim; intro cap
    apply Entails.sepExists_elim; intro ptr
    let vh := unpack64 cap ++ unpack64 ptr ++ unpack64 (BitVec.ofNat 64 bs.length)
    have ha32 : ∀ d : BitVec 64,
        d + 8#64 + BitVec.ofNat 64 vh.length = d + 32#64 := by
      intro d; change d + 8#64 + 24#64 = d + 32#64; bv_omega
    have hcons : ∀ d : BitVec 64,
        ((d + 32#64) ↦₈ msgTypeByte t) ∗ ((d + 33#64) ↦ₛ tail) =
          ((d + 32#64) ↦ₛ (msgTypeByte t :: tail)) := by
      intro d
      have hd33 : d + 33#64 = d + 32#64 + 1#64 := by bv_omega
      rw [hd33, ← pointsToBytes_cons]
    have hrearrange :
        (a ↦₆₄ speWord 24) ∗
          (⌜∀ c : BitVec 64, vecU8 A c bs ⊢ strAt c⌝ ∗
            (((a + 8#64) ↦ₛ vh) ∗ vecU8Buf A cap ptr bs)) ∗
          ((a + 32#64) ↦₈ msgTypeByte t) ∗ (⌜tail.length = 15⌝ ∗ ((a + 33#64) ↦ₛ tail)) =
        ⌜tail.length = 15⌝ ∗ ⌜∀ c : BitVec 64, vecU8 A c bs ⊢ strAt c⌝ ∗
          (a ↦₆₄ speWord 24) ∗
          (((a + 8#64) ↦ₛ vh) ∗
            (((a + 32#64) ↦₈ msgTypeByte t) ∗ ((a + 33#64) ↦ₛ tail))) ∗
          vecU8Buf A cap ptr bs := by ac_rfl
    rw [hrearrange]
    apply Entails.pure_left; intro htail
    apply Entails.pure_left; intro hr
    rw [hcons a]
    refine Entails.sepExists_right
      (vh ++ (msgTypeByte t :: tail))
      (Entails.sepExists_right (vecU8Buf A cap ptr bs) ?_)
    rw [pointsToBytes_append (a + 8#64) vh (msgTypeByte t :: tail), ha32 a]
    refine Entails.pure_right ⟨by simp [vh, htail], fun b => ?_⟩ (Entails.refl _)
    rw [hrec_eq b, pointsToBytes_append (b + 8#64) vh (msgTypeByte t :: tail), ha32 b, ← hcons b]
    have hb :
        ((b ↦₆₄ speWord 24) ∗
          (((b + 8#64) ↦ₛ vh) ∗
            (((b + 32#64) ↦₈ msgTypeByte t) ∗ ((b + 33#64) ↦ₛ tail))) ∗
          vecU8Buf A cap ptr bs) =
        ((b ↦₆₄ speWord 24) ∗
          (((b + 8#64) ↦ₛ vh) ∗ vecU8Buf A cap ptr bs) ∗
          ((b + 32#64) ↦₈ msgTypeByte t) ∗ ((b + 33#64) ↦ₛ tail)) := by ac_rfl
    rw [hb]
    refine sepConj_mono_right (sepConj_mono ?_ (sepConj_mono_right
      (htail ▸ pointsToBytes_entails_memRegion (b + 33#64) tail)))
    refine Entails.trans ?_ (hr (b + 8#64))
    rw [vecU8_eq_bytes24_sep_buf A (b + 8#64) bs]
    exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem recordResultAt_err_sat {A : RustAlloc} {sp : BitVec 64} {e : SignalProtocolError}
    (hne : e ≠ .panic) {P Q : SepProp} {m : Memory}
    (h : m ⊨ P ∗ (recordResultAt A (sp + 0x4b0#64) (.error e) ∗ Q)) :
    ∃ (w21 : BitVec 32) (w0 w1 : BitVec 64) (w2 : BitVec 32) (w3 w4 : BitVec 64)
      (bs : List (BitVec 8)) (H : SepProp),
      bs.length = 36 ∧
      bs = unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4 ∧
      (∀ r : BitVec 64,
        ((r ↦₆₄ recordResultTag (.error e)) ∗ ((r + 8#64) ↦₃₂ w21) ∗
          ((r + 12#64) ↦ₛ bs) ∗ H) ⊢
        apiDecResultAt A r (.error (.protocol e))) ∧
      (m ⊨ P ∗
        ((((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗
          ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗
          ((sp + 0x4c4#64) ↦₆₄ w1) ∗
          ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          ((sp + 0x4d0#64) ↦₆₄ w3) ∗
          ((sp + 0x4d8#64) ↦₆₄ w4) ∗
          H) ∗ Q)) := by
  have h1 := Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (recordResultAt_err_inline_40 A (sp + 0x4b0#64) e hne))) h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h1
  obtain ⟨bs40, H, h1⟩ := h1
  have h1' : m ⊨ ⌜bs40.length = 40 ∧ ∀ b : BitVec 64,
      ((b ↦₆₄ recordResultTag (.error e)) ∗ ((b + 8#64) ↦ₛ bs40) ∗ H) ⊢
        recordResultAt A b (.error e)⌝ ∗
      (P ∗ (((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b0#64 + 8#64) ↦ₛ bs40) ∗ H ∗ Q)) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  rw [satisfies_pure_sepConj] at h1'
  obtain ⟨⟨hbs40, hreassemble⟩, hmem⟩ := h1'
  have htake4 : (bs40.take 4).length = 4 := by simp [hbs40]
  have hdrop4 : (bs40.drop 4).length = 36 := by simp [hbs40]
  obtain ⟨w21, hw21⟩ := exists_unpack32_of_length_4 htake4
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36_regionErr hdrop4
  have hbs40_eq : bs40 = unpack32 w21 ++ bs40.drop 4 := by
    rw [← hw21]
    exact (List.take_append_drop 4 bs40).symm
  have hsplit_b : ∀ b : BitVec 64,
      ((b + 8#64) ↦ₛ bs40) = ((b + 8#64) ↦₃₂ w21) ∗ ((b + 12#64) ↦ₛ bs40.drop 4) := by
    intro b
    have hb12 : b + 8#64 + BitVec.ofNat 64 (unpack32 w21).length = b + 12#64 := by
      rw [unpack32_length]; bv_omega
    conv_lhs => rw [hbs40_eq, pointsToBytes_append, hb12, ← pointsTo32_eq_pointsToBytes]
  refine ⟨w21, w0, w1, w2, w3, w4, bs40.drop 4, H, hdrop4, hbs_eq, fun r => ?_, ?_⟩
  · dsimp only [apiDecResultAt]
    refine Entails.trans ?_ (hreassemble r)
    rw [hsplit_b r]
    exact Entails.of_eq (by ac_rfl)
  · have h4b8 : sp + 0x4b0#64 + 8#64 = sp + 0x4b8#64 := by bv_omega
    have h4bc : sp + 0x4b0#64 + 12#64 = sp + 0x4bc#64 := by bv_omega
    rw [hsplit_b (sp + 0x4b0#64), h4b8, h4bc, hbs_eq,
        pointsToBytes_36_regionErr_eq (sp + 0x4bc#64) w0 w1 w2 w3 w4] at hmem
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem

theorem record_some_entails_droppable (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (sp + 0x138#64) G st ⊢
      droppableRecordAt A (sp + 0x120#64) (some (G, st)) := by
  unfold droppableRecordAt prevBufAt
  have hvec :
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x120#64) prevCap prevPtr [] =
      ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] := by
    unfold vecAt vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_nil, sepConj_assoc]
  have h38 : sp + 0x120#64 + 0x18#64 = sp + 0x138#64 := by bv_omega
  rw [h38]
  refine Entails.trans ?_
    (sepConj_mono_left
      (Entails.sepExists_right prevCap
        (Entails.sepExists_right prevPtr (Entails.of_eq hvec.symm))))
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. 24-Byte `vecU8` Decomposition for the `Ok` Branch -/

theorem exists_split_24_d4 {bs : List (BitVec 8)} (h : bs.length = 24) :
    ∃ (w21 : BitVec 32) (w0 w1 : BitVec 64) (w2 : BitVec 32),
      bs = unpack32 w21 ++ unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 := by
  have h0 : (bs.take 4).length = 4 := by simp [h]
  have h1 : ((bs.drop 4).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 12).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 20).length = 4 := by simp [h]
  obtain ⟨w21, hw21⟩ := exists_unpack32_of_length_4 h0
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h1
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h2
  obtain ⟨w2, hw2⟩ := exists_unpack32_of_length_4 h3
  refine ⟨w21, w0, w1, w2, ?_⟩
  rw [← hw21, ← hw0, ← hw1, ← hw2]
  simp only [List.append_assoc]
  have s3 : (bs.drop 12).take 8 ++ bs.drop 20 = bs.drop 12 := by
    have := List.take_append_drop 8 (bs.drop 12)
    rwa [List.drop_drop] at this
  have s2 : (bs.drop 4).take 8 ++ bs.drop 12 = bs.drop 4 := by
    have := List.take_append_drop 8 (bs.drop 4)
    rwa [List.drop_drop] at this
  rw [s3, s2, List.take_append_drop]

theorem pointsToBytes_24_d4_eq (a : BitVec 64) (w21 : BitVec 32) (w0 w1 : BitVec 64)
    (w2 : BitVec 32) :
    (a ↦ₛ (unpack32 w21 ++ unpack64 w0 ++ unpack64 w1 ++ unpack32 w2)) =
    (a ↦₃₂ w21) ∗ ((a + 4#64) ↦₆₄ w0) ∗ ((a + 12#64) ↦₆₄ w1) ∗ ((a + 20#64) ↦₃₂ w2) := by
  simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack64_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem recordResultAt_ok_sat {A : RustAlloc} {sp : BitVec 64} {pt : List (BitVec 8)}
    {P Q : SepProp} {m : Memory}
    (h : m ⊨ P ∗ (recordResultAt A (sp + 0x4b0#64) (.ok pt) ∗ Q)) :
    ∃ (cap ptr : BitVec 64) (w21 : BitVec 32) (w0 w1 : BitVec 64) (w2 : BitVec 32),
      (∀ a : BitVec 64,
        ((a ↦₃₂ w21) ∗ ((a + 4#64) ↦₆₄ w0) ∗ ((a + 12#64) ↦₆₄ w1) ∗
          ((a + 20#64) ↦₃₂ w2) ∗ vecU8Buf A cap ptr pt) ⊢
          vecU8 A a pt) ∧
      (m ⊨ P ∗
        ((((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗
          ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗
          ((sp + 0x4c4#64) ↦₆₄ w1) ∗
          ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          memRegion (sp + 0x4d0#64) 16 ∗
          vecU8Buf A cap ptr pt) ∗ Q)) := by
  dsimp only [recordResultAt, vecResultAt] at h
  have h4b8 : sp + 0x4b0#64 + 8#64 = sp + 0x4b8#64 := by bv_omega
  have h4d0 : sp + 0x4b0#64 + 32#64 = sp + 0x4d0#64 := by bv_omega
  rw [h4b8, h4d0, vecU8_eq_bytes24_sep_buf A (sp + 0x4b8#64) pt] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h
  obtain ⟨cap, ptr, h⟩ := h
  let vh := unpack64 cap ++ unpack64 ptr ++ unpack64 (BitVec.ofNat 64 pt.length)
  have hvh_len : vh.length = 24 := by simp [vh]
  obtain ⟨w21, w0, w1, w2, hvh_eq⟩ := exists_split_24_d4 hvh_len
  refine ⟨cap, ptr, w21, w0, w1, w2, fun a => ?_, ?_⟩
  · rw [vecU8_eq_bytes24_sep_buf A a pt]
    refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
    change ((a ↦₃₂ w21) ∗ ((a + 4#64) ↦₆₄ w0) ∗ ((a + 12#64) ↦₆₄ w1) ∗
        ((a + 20#64) ↦₃₂ w2) ∗ vecU8Buf A cap ptr pt) ⊢
      (a ↦ₛ vh) ∗ vecU8Buf A cap ptr pt
    rw [hvh_eq, pointsToBytes_24_d4_eq a w21 w0 w1 w2]
    exact Entails.of_eq (by ac_rfl)
  · change m ⊨ P ∗
      ((((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ (((sp + 0x4b8#64) ↦ₛ vh) ∗ vecU8Buf A cap ptr pt) ∗
        memRegion (sp + 0x4d0#64) 16) ∗ Q) at h
    rw [hvh_eq, pointsToBytes_24_d4_eq (sp + 0x4b8#64) w21 w0 w1 w2] at h
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h

theorem slot290_split (sp : BitVec 64) :
    memRegion (sp + 0x290#64) 24 =
      (∃∗ p0 : BitVec 32, (sp + 0x290#64) ↦₃₂ p0) ∗
      (∃∗ p1 : BitVec 64, (sp + 0x294#64) ↦₆₄ p1) ∗
      (∃∗ p2 : BitVec 64, (sp + 0x29c#64) ↦₆₄ p2) ∗
      (∃∗ p3 : BitVec 32, (sp + 0x2a4#64) ↦₃₂ p3) := by
  rw [memRegion_split (sp + 0x290#64) 4 20 (by decide),
      memRegion_split (sp + 0x290#64 + 4#64) 8 12 (by decide),
      memRegion_split (sp + 0x290#64 + 4#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]

theorem slot4b0_ok_fold_memRegion (sp : BitVec 64) (w21 : BitVec 32) (w0 w1 : BitVec 64)
    (w2 : BitVec 32) :
    ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
      ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
      memRegion (sp + 0x4d0#64) 16 ⊢
      memRegion (sp + 0x4b0#64) 0x30 := by
  rw [memRegion_split (sp + 0x4b0#64) 8 40 (by decide),
      memRegion_split (sp + 0x4b0#64 + 8#64) 24 16 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h24 :
      ((sp + 0x4b8#64) ↦₃₂ w21) ∗ ((sp + 0x4bc#64) ↦₆₄ w0) ∗
        ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ⊢
      memRegion (sp + 0x4b8#64) 24 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x4b8#64)
      (unpack32 w21 ++ unpack64 w0 ++ unpack64 w1 ++ unpack32 w2)
    rw [pointsToBytes_24_d4_eq] at h
    simp only [List.length_append, unpack32_length, unpack64_length,
      BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hreord :
      ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        memRegion (sp + 0x4d0#64) 16 =
      ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗
        (((sp + 0x4b8#64) ↦₃₂ w21) ∗ ((sp + 0x4bc#64) ↦₆₄ w0) ∗
          ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2)) ∗
        memRegion (sp + 0x4d0#64) 16 := by ac_rfl
  rw [hreord]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono_left h24)

/-! ## 5. `sessionStateAt`, `remoteIdentityKey`, and `expect_failed` Helpers -/

def vecGhostRestAt (A : RustAlloc) (g : VecGhost) (p : BitVec 64) : SepProp :=
  ((p + 8#64) ↦₆₄ g.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
    ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
    (if g.cap = 0 then emp
     else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
       memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

theorem vecGhostAt_split_cap (A : RustAlloc) (g : VecGhost) (p : BitVec 64) :
    vecGhostAt A g p = (p ↦₆₄ g.cap) ∗ vecGhostRestAt A g p := by
  unfold vecGhostAt vecU8At vecHeader vecGhostRestAt
  ac_rfl

theorem vecGhostRestAt_cap_lt {A : RustAlloc} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    {m : Memory} (h : m ⊨ vecGhostRestAt A g p ∗ R) : g.cap.toNat < 2 ^ 63 := by
  unfold vecGhostRestAt at h
  have h1 := Satisfies.of_sep_left h
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.of_sep_right h2
  have h4 := Satisfies.of_sep_left h3
  rw [satisfies_pure] at h4
  exact h4.2.1

def sessionStateRemExposedAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
    vecGhostRestAt A G.localIk ss ∗
    vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
    vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
      (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + 0x60#64) ∗
    vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
    optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
    ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
    ((ss + 0x150#64) ↦ₛ G.regIds)

theorem sessionStateAt_expose_rem (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      (ss ↦₆₄ G.localIk.cap) ∗
      vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
      sessionStateRemExposedAt A ss G st := by
  unfold sessionStateAt sessionStateRemExposedAt
  rw [vecGhostAt_split_cap A G.localIk ss]
  ac_rfl

theorem sessionStateAt_rem_inv {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))} {m : Memory} {P R : SepProp}
    (h : m ⊨ P ∗ (sessionStateAt A ss G st ∗ R)) :
    match st.remoteIdentity with
    | none => G.remoteIk.bytes = []
    | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey := by
  have h1 := Satisfies.of_sep_right h
  have h2 := Satisfies.of_sep_left h1
  unfold sessionStateAt at h2
  have h3 := Satisfies.of_sep_left h2
  rw [satisfies_pure] at h3
  exact h3.2.1

theorem sessionStateAt_localIk_cap_lt {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))} {m : Memory} {P R : SepProp}
    (h : m ⊨ P ∗ (sessionStateAt A ss G st ∗ R)) : G.localIk.cap.toNat < 2 ^ 63 := by
  have h1 := Satisfies.of_sep_right h
  have h2 := Satisfies.of_sep_left h1
  rw [sessionStateAt_expose_rem] at h2
  have h3 := Satisfies.of_sep_right h2
  have h4 := Satisfies.of_sep_right h3
  unfold sessionStateRemExposedAt at h4
  have h5 := Satisfies.of_sep_right h4
  exact vecGhostRestAt_cap_lt h5

theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

theorem remoteIdentityKey_ok_at_msgDecrypt {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr msgDecryptName + 0x1fa0#64 +
        bv% (((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "session_message_decrypt_signal" - 8096) % 2 ^ 64)))
      (Getters.remoteIdentityKeySpec A img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff msgDecryptName) + 0x1fa0#64 +
      bv% (((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "session_message_decrypt_signal" - 8096) % 2 ^ 64)) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff Getters.remoteIdentityKeyName) := by
    simp only [arm64_norm]
  have haddr :
      (tripleRatchetProgAt img.base C ctl abs).fnAddr msgDecryptName + 0x1fa0#64 +
        bv% (((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "session_message_decrypt_signal" - 8096) % 2 ^ 64)) =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr Getters.remoteIdentityKeyName := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 64 _), hk]
  rwa [haddr]

def remoteIdentityTag : Option IdentityKey → BitVec 8
  | none => 0#8
  | some _ => 1#8

theorem remoteIdentityOkAt_unified (a : BitVec 64) (rem : Option IdentityKey) :
    Getters.remoteIdentityOkAt a rem ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 32 ∧ (∀ ik, rem = some ik → bs = ik.publicKey.bytes.toList)⌝ ∗
        (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ remoteIdentityTag rem) ∗ ((a + 2#64) ↦ₛ bs) := by
  cases rem with
  | none =>
    dsimp only [Getters.remoteIdentityOkAt, remoteIdentityTag]
    rw [memRegion_eq_exists_bytes (a + 2#64) 32 (by decide),
        sepExists_sepConj_right, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    have h1 : (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ (⌜bs.length = 32⌝ ∗ ((a + 2#64) ↦ₛ bs)) =
        ⌜bs.length = 32⌝ ∗ (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦ₛ bs) := by ac_rfl
    rw [h1]
    apply Entails.pure_left; intro hlen
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨hlen, fun _ h => by cases h⟩ (Entails.refl _)
  | some ik =>
    dsimp only [Getters.remoteIdentityOkAt, remoteIdentityTag]
    refine Entails.sepExists_right ik.publicKey.bytes.toList ?_
    refine Entails.pure_right ⟨ik.publicKey.bytes.toList_length, ?_⟩ (Entails.refl _)
    rintro _ ⟨rfl⟩; rfl

theorem slot5f0_fold_memRegion (sp : BitVec 64) (b0 b1 : BitVec 8)
    (k0 k1 k2 k3 : BitVec 64) :
    ((sp + 0x5f0#64) ↦₈ b0) ∗ ((sp + 0x5f1#64) ↦₈ b1) ∗
      ((sp + 0x5f2#64) ↦₆₄ k0) ∗ ((sp + 0x5fa#64) ↦₆₄ k1) ∗
      ((sp + 0x602#64) ↦₆₄ k2) ∗ ((sp + 0x60a#64) ↦₆₄ k3) ⊢
      memRegion (sp + 0x5f0#64) 34 := by
  rw [memRegion_split (sp + 0x5f0#64) 1 33 (by decide),
      memRegion_split (sp + 0x5f0#64 + 1#64) 1 32 (by decide),
      memRegion_split (sp + 0x5f0#64 + 1#64 + 1#64) 8 24 (by decide),
      memRegion_split (sp + 0x5f0#64 + 1#64 + 1#64 + 8#64) 8 16 (by decide),
      memRegion_split (sp + 0x5f0#64 + 1#64 + 1#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (pointsTo64_entails_memRegion _ _)))))

theorem slotca0_split (sp : BitVec 64) :
    memRegion (sp + 0xca0#64) 32 =
      (∃∗ c0 : BitVec 64, (sp + 0xca0#64) ↦₆₄ c0) ∗
      (∃∗ c1 : BitVec 64, (sp + 0xca8#64) ↦₆₄ c1) ∗
      (∃∗ c2 : BitVec 64, (sp + 0xcb0#64) ↦₆₄ c2) ∗
      (∃∗ c3 : BitVec 64, (sp + 0xcb8#64) ↦₆₄ c3) := by
  rw [memRegion_split (sp + 0xca0#64) 8 24 (by decide),
      memRegion_split (sp + 0xca0#64 + 8#64) 8 16 (by decide),
      memRegion_split (sp + 0xca0#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]

theorem slotca0_fold_memRegion (sp : BitVec 64) (k0 k1 k2 k3 : BitVec 64) :
    ((sp + 0xca0#64) ↦₆₄ k0) ∗ ((sp + 0xca8#64) ↦₆₄ k1) ∗
      ((sp + 0xcb0#64) ↦₆₄ k2) ∗ ((sp + 0xcb8#64) ↦₆₄ k3) ⊢
      memRegion (sp + 0xca0#64) 32 := by
  rw [slotca0_split sp]
  exact sepConj_mono (Entails.sepExists_right k0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right k1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right k2 (Entails.refl _))
        (Entails.sepExists_right k3 (Entails.refl _))))

theorem panic_at_expect_failed_msgDecrypt (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr msgDecryptName + bv% (ls_off% "core::option::expect_failed" - ls_off% "session_message_decrypt_signal")) = some Rust.panicked :=
  panic_at_sym b C ctl abs msgDecryptName "core::option::expect_failed" num% (ls_off% "core::option::expect_failed" - ls_off% "session_message_decrypt_signal")
    (by simp only [arm64_norm]) (hp := by decide +kernel)

/-! ## Relocatable `[LibsignalPlacement]` Helpers -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

theorem panic_at_expect_failed_msgDecrypt_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hpan : H lsExpectFailedSym = some Rust.panicked) :
    (lsProg_197 H).externAt? (lsρ lsExpectFailedSym) = some Rust.panicked := by
  dsimp only [lsProg_197]
  rwa [ls_externAt?_of_mem (prog := (blkPC_197).rebase (blkPl_197).base H)
    (i := 197) (sym := lsExpectFailedSym) (by decide)]

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome




