/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Instruction decode lemmas for `SegPostNone` (`+0x1f50..+0x1f70` + TE `+0x20b4..+0x20d4`) -/

gen_decodes libsignalSessionCode_tree messageDecryptPostNoneBin [(ls_off% "session_message_decrypt_signal" + 8016) → (ls_off% "session_message_decrypt_signal" + 8044), (ls_off% "session_message_decrypt_signal" + 8372) → (ls_off% "session_message_decrypt_signal" + 8400)]

/-! ## 2. 36-Byte TE Copy Decomposition (`16 + 4 + 16`) and BitVec Helpers -/

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ w : BitVec 32, bs = unpack32 w := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, (unpack32_pack32 b0 b1 b2 b3).symm⟩

theorem exists_split_36_regionErr {bs : List (BitVec 8)} (h : bs.length = 36) :
    ∃ (w0 w1 : BitVec 64) (w2 : BitVec 32) (w3 w4 : BitVec 64),
      bs = unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4 := by
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 4).length = 4 := by simp [h]
  have h3 : ((bs.drop 20).take 8).length = 8 := by simp [h]
  have h4 : (bs.drop 28).length = 8 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 h0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 h1
  obtain ⟨w2, hw2⟩ := exists_unpack32_of_length_4 h2
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 h3
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h4
  refine ⟨w0, w1, w2, w3, w4, ?_⟩
  rw [← hw0, ← hw1, ← hw2, ← hw3, ← hw4]
  simp only [List.append_assoc]
  have s4 : (bs.drop 20).take 8 ++ bs.drop 28 = bs.drop 20 := by
    have := List.take_append_drop 8 (bs.drop 20)
    rwa [List.drop_drop] at this
  have s3 : (bs.drop 16).take 4 ++ bs.drop 20 = bs.drop 16 := by
    have := List.take_append_drop 4 (bs.drop 16)
    rwa [List.drop_drop] at this
  have s2 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
    have := List.take_append_drop 8 (bs.drop 8)
    rwa [List.drop_drop] at this
  rw [s4, s3, s2, List.take_append_drop]

theorem pointsToBytes_36_regionErr_eq (a : BitVec 64) (w0 w1 : BitVec 64) (w2 : BitVec 32)
    (w3 w4 : BitVec 64) :
    (a ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4)) =
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₃₂ w2) ∗
      ((a + 20#64) ↦₆₄ w3) ∗ ((a + 28#64) ↦₆₄ w4) := by
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem decryptionFailed_slot_36_eq (p : BitVec 64) (cap ptr : BitVec 64) (t : MessageType)
    (pad : List (BitVec 8)) :
    ((p + 12#64) ↦ₛ
      (unpack32 (cap.extractLsb' 32 32) ++ unpack64 ptr ++
        unpack64 (BitVec.ofNat 64 decryptionFailedStr.length) ++ [msgTypeByte t] ++ pad)) =
    ((p + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
      ((p + 16#64) ↦₆₄ ptr) ∗
      ((p + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
      ((p + 32#64) ↦₈ msgTypeByte t) ∗
      ((p + 33#64) ↦ₛ pad) := by
  simp only [List.append_assoc, List.singleton_append, pointsToBytes_append, pointsToBytes_cons,
    unpack32_length, unpack64_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem resWord1_ubfm_eq (w21 : BitVec 32) :
    resWord1
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w21 >>> 8)))
      (BitVec.zeroExtend 64 w21) =
    w21 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [resWord1, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  have h64 : i < 64 := by omega
  by_cases h8 : i < 8
  · simp [h8, hi, h64]
  · have hi8_24 : i - 8 < 24 := by omega
    have hi8_32 : i - 8 < 32 := by omega
    have hi8_64 : i - 8 < 64 := by omega
    have hadd_eq : 8 + (i - 8) = i := by omega
    simp [h8, hi8_24, hi8_32, hi8_64, hadd_eq, hi, h64]

def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8_eq_exists_buf (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs =
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Buf
  simp only [sepConj_assoc]

theorem recordResultAt_decryptionFailed_eq (A : RustAlloc) (r : BitVec 64) :
    recordResultAt A r (.error (.invalidMessage .whisper .decryptionFailed)) =
      ∃∗ pad : List (BitVec 8), ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜pad.length = 15⌝ ∗
        ((r ↦₆₄ speWord 24) ∗
          ((r + 8#64) ↦₆₄ cap) ∗
          ((r + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((r + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
          ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
          ((r + 33#64) ↦ₛ pad) ∗
          vecU8Buf A cap ptr decryptionFailedStr) := by
  dsimp only [recordResultAt]
  rw [vecU8_eq_exists_buf A (r + 8#64) decryptionFailedStr,
      memRegion_eq_exists_bytes (r + 33#64) 15 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun pad => congrArg sepExists (funext fun cap =>
    congrArg sepExists (funext fun ptr => ?_)))
  ac_rfl

theorem recordResultAt_decryptionFailed_sat {A : RustAlloc} {r : BitVec 64} {P Q : SepProp}
    {m : Memory}
    (h : m ⊨ P ∗ (recordResultAt A r (.error (.invalidMessage .whisper .decryptionFailed)) ∗ Q)) :
    ∃ (pad : List (BitVec 8)) (cap ptr : BitVec 64),
      pad.length = 15 ∧
      (m ⊨ P ∗
        (((r ↦₆₄ speWord 24) ∗
          ((r + 8#64) ↦₆₄ cap) ∗
          ((r + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((r + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
          ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
          ((r + 33#64) ↦ₛ pad) ∗
          vecU8Buf A cap ptr decryptionFailedStr) ∗ Q)) := by
  rw [recordResultAt_decryptionFailed_eq A r] at h
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at h
  obtain ⟨pad, cap, ptr, h⟩ := h
  have h' : m ⊨ ⌜pad.length = 15⌝ ∗
      (P ∗ (((r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₆₄ cap) ∗ ((r + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((r + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
        ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗ ((r + 33#64) ↦ₛ pad) ∗
        vecU8Buf A cap ptr decryptionFailedStr) ∗ Q)) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) h
  rw [satisfies_pure_sepConj] at h'
  exact ⟨pad, cap, ptr, h'.1, h'.2⟩

theorem staged36_regionErr_entails_memRegion (sp : BitVec 64) (w0 w1 : BitVec 64) (w2 : BitVec 32)
    (w3 w4 : BitVec 64) :
    ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
      ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ⊢
      memRegion (sp + 0x4bc#64) 0x24 := by
  have h := pointsToBytes_entails_memRegion (sp + 0x4bc#64)
    (unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4)
  rw [pointsToBytes_36_regionErr_eq] at h
  simp only [List.length_append, unpack64_length, unpack32_length,
    BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

theorem slot48_fold_memRegion (sp : BitVec 64) (tag : BitVec 64) (w21 : BitVec 32)
    (w0 w1 : BitVec 64) (w2 : BitVec 32) (w3 w4 : BitVec 64) :
    ((sp + 0x4b0#64) ↦₆₄ tag) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
      ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
      ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ⊢
      memRegion (sp + 0x4b0#64) 0x30 := by
  rw [memRegion_split (sp + 0x4b0#64) 8 40 (by decide),
      memRegion_split (sp + 0x4b0#64 + 8#64) 4 36 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo32_entails_memRegion _ _) ?_
  exact staged36_regionErr_entails_memRegion sp w0 w1 w2 w3 w4

theorem scratch20_split (sp : BitVec 64) :
    memRegion (sp + 0x490#64) 0x14 =
      (∃∗ t0 : BitVec 64, (sp + 0x490#64) ↦₆₄ t0) ∗
      (∃∗ t1 : BitVec 64, (sp + 0x498#64) ↦₆₄ t1) ∗
      (∃∗ t2 : BitVec 32, (sp + 0x4a0#64) ↦₃₂ t2) := by
  rw [memRegion_split (sp + 0x490#64) 8 12 (by decide),
      memRegion_split (sp + 0x490#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]

theorem scratch20_fold (sp : BitVec 64) (w0 w1 : BitVec 64) (w2 : BitVec 32) :
    ((sp + 0x490#64) ↦₆₄ w0) ∗ ((sp + 0x498#64) ↦₆₄ w1) ∗ ((sp + 0x4a0#64) ↦₃₂ w2) ⊢
      memRegion (sp + 0x490#64) 0x14 := by
  rw [scratch20_split sp]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem dst36_split (sp : BitVec 64) :
    memRegion (sp + 0x580#64) 0x24 =
      (∃∗ d0 : BitVec 64, (sp + 0x580#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 0x588#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 32, (sp + 0x590#64) ↦₃₂ d2) ∗
      (∃∗ d3 : BitVec 64, (sp + 0x594#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (sp + 0x59c#64) ↦₆₄ d4) := by
  rw [memRegion_split (sp + 0x580#64) 8 28 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64) 8 20 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64) 4 16 (by decide),
      memRegion_split (sp + 0x580#64 + 8#64 + 8#64 + 4#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]

theorem dst36_fold (sp : BitVec 64) (w0 w1 : BitVec 64) (w2 : BitVec 32) (w3 w4 : BitVec 64)
    {bs : List (BitVec 8)}
    (hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack32 w2 ++ unpack64 w3 ++ unpack64 w4) :
    ((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₃₂ w2) ∗
      ((sp + 0x594#64) ↦₆₄ w3) ∗ ((sp + 0x59c#64) ↦₆₄ w4) ⊢
      ((sp + 0x580#64) ↦ₛ bs) := by
  subst hbs
  rw [pointsToBytes_36_regionErr_eq (sp + 0x580#64) w0 w1 w2 w3 w4]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _

theorem api_run_storeCall_ok {Addr PQ E α β : Type} (c : StoreCall Addr PQ) (a : α)
    (k : α → Api Addr PQ E β) :
    Api.run (storeCall c (.ok a) >>= k) = (ExceptT.run (k a)).run [c] := rfl

theorem exceptT_run_liftProtocol_error {Addr PQ E α β : Type} (e : SignalProtocolError)
    (k : α → Api Addr PQ E β) (s : List (StoreCall Addr PQ)) :
    (ExceptT.run (liftProtocol (.error e) >>= k)).run s = (.error (ApiError.ofProtocol e), s) := rfl

theorem model_of_load_current_none (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec : SessionRecord (List (BitVec 8)))
    (hload : ans.loadSession = .ok (some rec)) (hcur : rec.currentSession = none) :
    x.model C S uuidTryParse ans =
      (.error (.protocol (.invalidMessage .whisper .decryptionFailed)),
        [.loadSession x.rem.val]) ∧
    x.draws C ans = 0 := by
  refine ⟨?_, ?_⟩
  · unfold DecryptGhost.model messageDecryptSignal
    rw [hload, api_run_storeCall_ok]
    dsimp only [SessionRecord.tryDecryptFromRecord]
    rw [hcur, exceptT_run_liftProtocol_error]
    rfl
  · simp [DecryptGhost.draws, loadedSession, hload, hcur]

theorem tapeAt_entails_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  apply Entails.pure_left; intro _
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem record_none_entails_droppable (A : RustAlloc) (sp prevCap prevPtr : BitVec 64) :
    ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ⊢
      droppableRecordAt A (sp + 0x120#64) none := by
  unfold droppableRecordAt prevBufAt
  have hvec :
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x120#64) prevCap prevPtr [] =
      ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
        ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        vecBuf A 24 8 (fun (_ : Unit) _ => emp) prevCap prevPtr [] := by
    unfold vecAt vecHeader
    simp only [BitVec.add_assoc, BitVec.reduceAdd, List.length_nil, sepConj_assoc]
  have h38 : sp + 0x120#64 + 0x18#64 = sp + 0x138#64 := by bv_omega
  have h40 : sp + 0x120#64 + 0x20#64 = sp + 0x140#64 := by bv_omega
  rw [h38, h40]
  refine Entails.trans ?_
    (sepConj_mono_left
      (Entails.sepExists_right prevCap
        (Entails.sepExists_right prevPtr (Entails.of_eq hvec.symm))))
  exact Entails.of_eq (by ac_rfl)

theorem stackAt_root_join_wsCallee (sp : BitVec 64) :
    stackAt sp rootStack ∗
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) =
    stackAt sp wsCalleeStack := by
  simp only [stackAt]
  have hsplit := memRegion_split (sp - BitVec.ofNat 64 wsCalleeStack)
    (wsCalleeStack - rootStack) rootStack (by decide)
  rw [show (wsCalleeStack - rootStack) + rootStack = wsCalleeStack by decide] at hsplit
  have hadd :
      sp - BitVec.ofNat 64 wsCalleeStack + BitVec.ofNat 64 (wsCalleeStack - rootStack) =
      sp - BitVec.ofNat 64 rootStack := by
    dsimp only [wsCalleeStack, wsStack, entryStack, wsFrame, rootStack]; bv_omega
  rw [hsplit, hadd, sepConj_comm]

theorem segPostNoneV_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegPostNoneSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hH x ans R s0 s hPN hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hfrozen, hsym, hvregs⟩,
    hx26, hx28, rec, prevCap, prevPtr, hload, hscope, hcur, htrace, hmem⟩ := hPN
  have hentry := entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl) (abs := abs) hH.loads
    msgDecryptName
  have hfn : libsignalSessionCode.fnOff msgDecryptName = num% (ls_off% "session_message_decrypt_signal") :=
    CryptoVerification.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  unfold recordRegionExit at hpc
  rw [hentry] at hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have ⟨hmod, hdraws⟩ := model_of_load_current_none C S x ans rec hload hcur
  let sp := s0.sp - 0xee0#64
  let R' := decStoreExtra kit ikit st0 ist0 s0 ∗ R
  have hmem_grp :
      s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
            stackAt sp rootStack ∗ A.pool ∗ wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ R')) := by
    dsimp only [sp, R']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  obtain ⟨pad, cap, ptr, hpad_len, hmem⟩ := recordResultAt_decryptionFailed_sat hmem_grp
  clear hmem_grp
  let w21 := cap.extractLsb' 0 32
  let bs := unpack32 (cap.extractLsb' 32 32) ++ unpack64 ptr ++
    unpack64 (BitVec.ofNat 64 decryptionFailedStr.length) ++ [msgTypeByte .whisper] ++ pad
  have hbs_len : bs.length = 36 := by
    simp [bs, hpad_len]
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36_regionErr hbs_len
  have hslot_orig :
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b0#64 + 8#64) ↦₆₄ cap) ∗
        ((sp + 0x4b0#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((sp + 0x4b0#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
        ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
        ((sp + 0x4b0#64 + 33#64) ↦ₛ pad) ∗
        vecU8Buf A cap ptr decryptionFailedStr) =
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        vecU8Buf A cap ptr decryptionFailedStr) := by
    have h8 := pointsTo64_split32 (sp + 0x4b0#64 + 8#64) cap
    have h36 := decryptionFailed_slot_36_eq (sp + 0x4b0#64) cap ptr .whisper pad
    have h36_te := pointsToBytes_36_regionErr_eq (sp + 0x4b0#64 + 12#64) w0 w1 w2 w3 w4
    dsimp only [bs] at hbs_eq
    rw [hbs_eq, h36_te] at h36
    rw [h8]
    simp only [w21, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h36 ⊢
    have h36' := congrArg (· ∗ vecU8Buf A cap ptr decryptionFailedStr) h36.symm
    simp only [sepConj_assoc] at h36'
    rw [h36']
  have h300_split :
      memRegion (sp + 0x300#64) 0x1b0 =
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4e0_split :
      memRegion (sp + 0x4e0#64) 0x920 =
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x580#64) 0x24 ∗
          memRegion (sp + 0x5a4#64) 0x85c := by
    rw [memRegion_split (sp + 0x4e0#64) 0xa0 0x880 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0xa0#64) 0x24 0x85c (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hmem_act : s.mem ⊨
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
        vecU8Buf A cap ptr decryptionFailedStr ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsFixedV kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') := by
    have hws_eq :
        wsRegionFrameV img kit ikit x s0 prevCap prevPtr =
          wsFixedV kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x1b0 ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 := by
      unfold wsRegionFrameV wsFixedV
      dsimp only [sp]
      ac_rfl
    rw [hws_eq, hslot_orig, h300_split, h4e0_split] at hmem
    dsimp only [sp] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) (errJoinPC img false) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
        sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = speWord 24 ∧
        resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
    code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostNoneBin img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x1f50 0x20
    code_fetches_range CryptoVerification.libsignalSessionCode messageDecryptPostNoneBin img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn (num% (ls_off% "session_message_decrypt_signal")) 0x20b4 0x20
    unfold errJoinPC
    rw [ite_eq_right_iff.mpr nofun, hentry]
    dsimp only [tripleRatchetProgAt] at hpc ⊢
    generalize (libsignalSessionCode.rebase img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr msgDecryptName = entry at *
    examples_hide_fetches
    wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    dsimp only [recordResultTag, speWord] at hx28
    wp_steps
    apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
    apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (speWord 24) w21 w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (dst36_fold (s0.sp - 0xee0#64) w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, rfl, hal, rfl, ?_, ?_, ?_, ?_, ?_, hvregs⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      wp_norm_lhs
    · wp_norm_lhs
    · simp only [wp_norm, arm64_norm]
      exact resWord1_ubfm_eq w21
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, hal_sf, htr_sf,
    hx29_sf, hx27_sf, hx26_sf, hx28_sf, hres_w1, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hfrozen_sf : img.FrozenLoaded sf := hfrozen.of_keepsFrozen hsteps.keepsFrozen
  have hsym_sf : sf.symtab = img.symtab := hsteps.symtab_eq.trans hsym
  refine ⟨sf, hsteps, Or.inl ?_⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hfrozen_sf, hsym_sf, hvregs_sf⟩,
    hx26_sf, ?_, ans, none, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx28_sf]; decide
  · intro h; rw [hmod] at h; cases h
  · intro p h; rw [hmod] at h; cases h
  · intro r hr; rw [hload] at hr; cases hr; exact hscope
  · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
  · rw [hmod]; trivial
  · rw [htr_sf, htrace, hmod]; simp
  · have hstaged :
        ((sp + 0x580#64) ↦ₛ bs) ∗ vecU8Buf A cap ptr decryptionFailedStr ⊢
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 := by
      unfold StagedRes
      refine Entails.sepExists_right bs
        (Entails.sepExists_right (vecU8Buf A cap ptr decryptionFailedStr) ?_)
      refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
      rw [hmod, hx28_sf, hres_w1]
      dsimp only [apiDecResultAt, recordResultAt]
      rw [vecU8_eq_exists_buf A (r + 8#64) decryptionFailedStr]
      have h36 := decryptionFailed_slot_36_eq r cap ptr .whisper pad
      have h8 := pointsTo64_split32 (r + 8#64) cap
      have hpad_mem : ((r + 33#64) ↦ₛ pad) ⊢ memRegion (r + 33#64) 15 := by
        have h := pointsToBytes_entails_memRegion (r + 33#64) pad
        rwa [hpad_len] at h
      dsimp only [bs]
      rw [h36]
      refine Entails.trans ?_
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.sepExists_right cap
              (Entails.sepExists_right ptr (Entails.refl _)))))
      rw [h8]
      simp only [w21, BitVec.add_assoc, BitVec.reduceAdd]
      have hreord_r :
          (r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            (((r + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
              ((r + 33#64) ↦ₛ pad)) ∗
            vecU8Buf A cap ptr decryptionFailedStr =
          ((r ↦₆₄ speWord 24) ∗
            ((((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗ ((r + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              vecU8Buf A cap ptr decryptionFailedStr) ∗
            ((r + 32#64) ↦₈ msgTypeByte .whisper)) ∗
          ((r + 33#64) ↦ₛ pad) := by
        ac_rfl
      rw [hreord_r]
      refine Entails.trans (sepConj_mono_right hpad_mem) ?_
      exact Entails.of_eq (by ac_rfl)
    have h290_split :
        memRegion (sp + 0x290#64) 0x38 =
          memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
      rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h300_join :
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
          memRegion (sp + 0x4e0#64) 0xa0 =
        memRegion (sp + 0x300#64) 0x280 := by
      rw [memRegion_split (sp + 0x300#64) 0x190 0xf0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xdc (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0xd0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0xa0 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb :
        (memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∗
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          vecU8Buf A cap ptr decryptionFailedStr ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsFixedV kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') ⊢
        wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
          droppableRecordAt A (sp + 0x120#64) none ∗
          memRegion (sp + 0x290#64) 24 ∗
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
      have hwsEnv_eq :
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ logOff img ∗
            (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool =
          wsEnv A img x sp := by
        unfold wsEnv
        rw [stackAt_root_join_wsCallee sp]
      rw [hdraws, h290_split]
      have hreord_lhs :
          (memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            ((sp + 0x580#64) ↦ₛ bs)) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
            vecU8Buf A cap ptr decryptionFailedStr ∗
            memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsFixedV kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            (memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
            memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ R') =
          ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
              ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
            (((sp + 0x580#64) ↦ₛ bs) ∗ vecU8Buf A cap ptr decryptionFailedStr) ∗
            tapeAt ctl x.cur x.rest ∗
            (wsFixedV kit ikit x s0 sp ∗
              (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗ logOff img ∗
                (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
                A.pool) ∗
              wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
              memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
                memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
                memRegion (sp + 0x4e0#64) 0xa0) ∗
              memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗ R')) := by
        ac_rfl
      rw [hreord_lhs, hwsEnv_eq, h300_join]
      refine Entails.trans
        (sepConj_mono (record_none_entails_droppable A sp prevCap prevPtr)
          (sepConj_mono hstaged
            (sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)))) ?_
      exact Entails.of_eq (by ac_rfl)
    have hfin := Satisfies.mono hcomb hmf1
    rw [hmod] at hfin ⊢
    exact hfin

theorem segPostNone_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegPostNoneSpec img C A ctl uuidTryParse S encRecord abs :=
  segPostNoneV_ok

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem segPostNoneVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegPostNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro _hH x ans R s0 s hPN hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    hx26, hx28, rec, prevCap, prevPtr, hload, hscope, hcur, htrace, hmem⟩ := hPN
  have hpc' : s.pc = (blkPl_197).base + 8016#64 := hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have ⟨hmod, hdraws⟩ := model_of_load_current_none C S x ans rec hload hcur
  let sp := s0.sp - 0xee0#64
  let R' := decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  have hmem_grp :
      s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗ wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R')) := by
    dsimp only [sp, R']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  obtain ⟨pad, cap, ptr, hpad_len, hmem⟩ := recordResultAt_decryptionFailed_sat hmem_grp
  clear hmem_grp
  let w21 := cap.extractLsb' 0 32
  let bs := unpack32 (cap.extractLsb' 32 32) ++ unpack64 ptr ++
    unpack64 (BitVec.ofNat 64 decryptionFailedStr.length) ++ [msgTypeByte .whisper] ++ pad
  have hbs_len : bs.length = 36 := by
    simp [bs, hpad_len]
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36_regionErr hbs_len
  have hslot_orig :
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b0#64 + 8#64) ↦₆₄ cap) ∗
        ((sp + 0x4b0#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((sp + 0x4b0#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
        ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
        ((sp + 0x4b0#64 + 33#64) ↦ₛ pad) ∗
        vecU8Buf A cap ptr decryptionFailedStr) =
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        vecU8Buf A cap ptr decryptionFailedStr) := by
    have h8 := pointsTo64_split32 (sp + 0x4b0#64 + 8#64) cap
    have h36 := decryptionFailed_slot_36_eq (sp + 0x4b0#64) cap ptr .whisper pad
    have h36_te := pointsToBytes_36_regionErr_eq (sp + 0x4b0#64 + 12#64) w0 w1 w2 w3 w4
    dsimp only [bs] at hbs_eq
    rw [hbs_eq, h36_te] at h36
    rw [h8]
    simp only [w21, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h36 ⊢
    have h36' := congrArg (· ∗ vecU8Buf A cap ptr decryptionFailedStr) h36.symm
    simp only [sepConj_assoc] at h36'
    rw [h36']
  have h300_split :
      memRegion (sp + 0x300#64) 0x1b0 =
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc := by
    rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
        memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h4e0_split :
      memRegion (sp + 0x4e0#64) 0x920 =
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x580#64) 0x24 ∗
          memRegion (sp + 0x5a4#64) 0x85c := by
    rw [memRegion_split (sp + 0x4e0#64) 0xa0 0x880 (by decide),
        memRegion_split (sp + 0x4e0#64 + 0xa0#64) 0x24 0x85c (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hmem_act : s.mem ⊨
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
        vecU8Buf A cap ptr decryptionFailedStr ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ A.pool ∗
        wsFixedVPlaced kit ikit x s0 sp ∗
        ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
        memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
        memRegion x.ret 48 ∗ R') := by
    have hws_eq :
        wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr =
          wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x1b0 ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 := by
      unfold wsRegionFrameVPlaced wsFixedVPlaced
      dsimp only [sp]
      ac_rfl
    rw [hws_eq, hslot_orig, h300_split, h4e0_split] at hmem
    dsimp only [sp] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (lsProg_197 H) (errJoinPCPlaced false) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
        sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = speWord 24 ∧
        resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
    unfold errJoinPCPlaced
    rw [ite_eq_right_iff.mpr nofun]
    dsimp only [lsProg_197]
    wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    dsimp only [recordResultTag, speWord] at hx28
    wp_steps
    apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
    apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (speWord 24) w21 w0 w1 w2 w3 w4) (by sep_focus)
    apply SepWP.fold (dst36_fold (s0.sp - 0xee0#64) w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    refine ⟨?_, rfl, hal, rfl, ?_, ?_, ?_, ?_, ?_, hvregs⟩
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    · wp_norm_lhs
    · wp_norm_lhs
    · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      wp_norm_lhs
    · wp_norm_lhs
    · simp only [wp_norm, arm64_norm]
      exact resWord1_ubfm_eq w21
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, hal_sf, htr_sf,
    hx29_sf, hx27_sf, hx26_sf, hx28_sf, hres_w1, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
    hwp.elim hmem_act hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  refine ⟨sf, hsteps, Or.inl ?_⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hcrl_sf, hvregs_sf⟩,
    hx26_sf, ?_, ans, none, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx28_sf]; decide
  · intro h; rw [hmod] at h; cases h
  · intro p h; rw [hmod] at h; cases h
  · intro r hr; rw [hload] at hr; cases hr; exact hscope
  · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
  · rw [hmod]; trivial
  · rw [htr_sf, htrace, hmod]; simp
  · have hstaged :
        ((sp + 0x580#64) ↦ₛ bs) ∗ vecU8Buf A cap ptr decryptionFailedStr ⊢
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 := by
      unfold StagedRes
      refine Entails.sepExists_right bs
        (Entails.sepExists_right (vecU8Buf A cap ptr decryptionFailedStr) ?_)
      refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
      rw [hmod, hx28_sf, hres_w1]
      dsimp only [apiDecResultAt, recordResultAt]
      rw [vecU8_eq_exists_buf A (r + 8#64) decryptionFailedStr]
      have h36 := decryptionFailed_slot_36_eq r cap ptr .whisper pad
      have h8 := pointsTo64_split32 (r + 8#64) cap
      have hpad_mem : ((r + 33#64) ↦ₛ pad) ⊢ memRegion (r + 33#64) 15 := by
        have h := pointsToBytes_entails_memRegion (r + 33#64) pad
        rwa [hpad_len] at h
      dsimp only [bs]
      rw [h36]
      refine Entails.trans ?_
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.sepExists_right cap
              (Entails.sepExists_right ptr (Entails.refl _)))))
      rw [h8]
      simp only [w21, BitVec.add_assoc, BitVec.reduceAdd]
      have hreord_r :
          (r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            (((r + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
              ((r + 33#64) ↦ₛ pad)) ∗
            vecU8Buf A cap ptr decryptionFailedStr =
          ((r ↦₆₄ speWord 24) ∗
            ((((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗ ((r + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              vecU8Buf A cap ptr decryptionFailedStr) ∗
            ((r + 32#64) ↦₈ msgTypeByte .whisper)) ∗
          ((r + 33#64) ↦ₛ pad) := by
        ac_rfl
      rw [hreord_r]
      refine Entails.trans (sepConj_mono_right hpad_mem) ?_
      exact Entails.of_eq (by ac_rfl)
    have h290_split :
        memRegion (sp + 0x290#64) 0x38 =
          memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
      rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h300_join :
        memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
          memRegion (sp + 0x4e0#64) 0xa0 =
        memRegion (sp + 0x300#64) 0x280 := by
      rw [memRegion_split (sp + 0x300#64) 0x190 0xf0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xdc (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0xd0 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0xa0 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hcomb :
        (memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∗
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          vecU8Buf A cap ptr decryptionFailedStr ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsFixedVPlaced kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') ⊢
        wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
          droppableRecordAt A (sp + 0x120#64) none ∗
          memRegion (sp + 0x290#64) 24 ∗
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
      have hwsEnv_eq :
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
            (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool =
          wsEnvPlaced A x sp := by
        unfold wsEnvPlaced
        rw [stackAt_root_join_wsCallee sp]
      rw [hdraws, h290_split]
      have hreord_lhs :
          (memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            ((sp + 0x580#64) ↦ₛ bs)) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
            vecU8Buf A cap ptr decryptionFailedStr ∗
            memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            (memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
            memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ R') =
          ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
              ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
            (((sp + 0x580#64) ↦ₛ bs) ∗ vecU8Buf A cap ptr decryptionFailedStr) ∗
            tapeAt ctl x.cur x.rest ∗
            (wsFixedVPlaced kit ikit x s0 sp ∗
              (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
                protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
                (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
                A.pool) ∗
              wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
              memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
                memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
                memRegion (sp + 0x4e0#64) 0xa0) ∗
              memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗ R')) := by
        ac_rfl
      rw [hreord_lhs, hwsEnv_eq, h300_join]
      refine Entails.trans
        (sepConj_mono (record_none_entails_droppable A sp prevCap prevPtr)
          (sepConj_mono hstaged
            (sepConj_mono_left (tapeAt_entails_tapeAfter_zero ctl x.cur x.rest)))) ?_
      exact Entails.of_eq (by ac_rfl)
    have hfin := Satisfies.mono hcomb hmf1
    rw [hmod] at hfin ⊢
    exact hfin

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone
