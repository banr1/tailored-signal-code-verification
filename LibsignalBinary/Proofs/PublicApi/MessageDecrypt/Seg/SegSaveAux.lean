/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Helpers for `SegSave`

Instruction decode lemmas, `.rodata` `"store hook"` repack lemmas, `StagedRes` and stack helpers,
and `messageDecrypt_call_panic` call tactics for `SegSave`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Decode Lemmas (`+0x2150..+0x21b0`, `+0x2334..+0x2388`, `+0x23c8..+0x23dc`) -/

gen_decodes libsignalSessionCode_tree segSaveBin [(ls_off% "session_message_decrypt_signal" + 8528) → (ls_off% "session_message_decrypt_signal" + 8620), (ls_off% "session_message_decrypt_signal" + 9012) → (ls_off% "session_message_decrypt_signal" + 9092),
    (ls_off% "session_message_decrypt_signal" + 9160) → (ls_off% "session_message_decrypt_signal" + 9176)]

/-! ## 2. Shared Repack, `.rodata` `"store hook"`, and `StagedRes` Lemmas -/

theorem pointsTo64_append32 (hi lo : BitVec 32) (a : BitVec 64) :
    (a ↦₆₄ (hi ++ lo)) = ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) := by
  rw [pointsTo64_split32, BitVec.extractLsb'_append_eq_right, BitVec.extractLsb'_append_eq_left]

theorem out_repack (o w1 w2 w3 w4 w5 : BitVec 64) :
    ((o + 8#64) ↦₆₄ w1) ∗ ((o + 16#64) ↦₆₄ w2) ∗ ((o + 24#64) ↦₆₄ w3) ∗
        ((o + 32#64) ↦₆₄ w4) ∗ ((o + 40#64) ↦₆₄ w5) =
      ((o + 8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((o + 12#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((o + 20#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((o + 28#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((o + 36#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((o + 44#64) ↦₃₂ w5.extractLsb' 32 32) := by
  simp only [pointsTo64_append32]
  simp only [pointsTo64_split32, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem out_repack_sp (sp w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 1528#64) ↦₆₄ w1) ∗ ((sp + 1536#64) ↦₆₄ w2) ∗ ((sp + 1544#64) ↦₆₄ w3) ∗
        ((sp + 1552#64) ↦₆₄ w4) ∗ ((sp + 1560#64) ↦₆₄ w5) =
      ((sp + 1528#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        ((sp + 1532#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
        ((sp + 1540#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
        ((sp + 1548#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
        ((sp + 1556#64) ↦₆₄ (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)) ∗
        ((sp + 1564#64) ↦₃₂ w5.extractLsb' 32 32) := by
  have h := out_repack (sp + 1520#64) w1 w2 w3 w4 w5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

/-- 36-byte payload tail (`+0xc..+0x30`) packed from four 64-bit words and one 32-bit word. -/
def bytes36 (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) : List (BitVec 8) :=
  unpack64 o2 ++ (unpack64 o3 ++ (unpack64 o4 ++ (unpack64 o5 ++ unpack32 o6)))

theorem bytes36_length (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    (bytes36 o2 o3 o4 o5 o6).length = 36 := by
  simp only [bytes36, List.length_append, unpack64_length, unpack32_length]

theorem words36At_eq_pointsToBytes (a o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    ((a ↦₆₄ o2) ∗ ((a + 8#64) ↦₆₄ o3) ∗ ((a + 16#64) ↦₆₄ o4) ∗
      ((a + 24#64) ↦₆₄ o5) ∗ ((a + 32#64) ↦₃₂ o6)) =
    (a ↦ₛ bytes36 o2 o3 o4 o5 o6) := by
  unfold bytes36
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [unpack64_length, BitVec.add_assoc, BitVec.reduceAdd,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

theorem resWord1_lsr8 (o1 : BitVec 32) :
    resWord1 ((o1 >>> 8#32).zeroExtend 64) (o1.zeroExtend 64) = o1 := by
  have hsh : o1 >>> 8#32 = o1 >>> (8 : Nat) := rfl
  rw [hsh]
  unfold resWord1
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, Nat.zero_add]
  split_ifs with h8
  · rw [decide_eq_true (by omega : i < 64), Bool.true_and, BitVec.getLsbD_eq_getElem hi]
  · rw [decide_eq_true (by omega : i - 8 < 64), Bool.true_and, ← BitVec.getLsbD_eq_getElem hi]
    exact congrArg o1.getLsbD (by omega)

theorem stagedRes_storeErr_intro (A : RustAlloc) (b x28 w20 w21 src w5 o2 o3 o4 o5 : BitVec 64)
    (o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64)
    (hw1 : resWord1 w20 w21 = (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32)
    (ho2 : o2 = (10#64 : BitVec 64).extractLsb' 0 32 ++ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 32 32)
    (ho3 : o3 = (1#64 : BitVec 64).extractLsb' 0 32 ++ (10#64 : BitVec 64).extractLsb' 32 32)
    (ho4 : o4 = (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 0 32 ++ (1#64 : BitVec 64).extractLsb' 32 32)
    (ho5 : o5 = w5.extractLsb' 0 32 ++ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 32 32)
    (ho6 : o6 = w5.extractLsb' 32 32) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  let w1 := b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
  let w2 := 10#64
  let w3 := 1#64
  let w4 := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)
  rw [words36At_eq_pointsToBytes]
  unfold StagedRes
  refine Entails.sepExists_right (bytes36 o2 o3 o4 o5 o6) ?_
  refine Entails.sepExists_right ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ?_
  refine Entails.pure_right ⟨bytes36_length o2 o3 o4 o5 o6, fun r => ?_⟩ (Entails.refl _)
  rw [hx28, hw1, ← words36At_eq_pointsToBytes]
  have hrep := (out_repack r w1 w2 w3 w4 w5).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep ⊢
  have hgrp :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
        (((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₃₂ w1.extractLsb' 0 32) ∗
          ((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) := by ac_rfl
  rw [hgrp, ho2, ho3, ho4, ho5, ho6, hrep]
  unfold apiDecResultAt apiErrAt strRefAt
  have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by decide +kernel
  have htag : (0x800000000000001A#64 : BitVec 64) = speWord speApplicationCallback := rfl
  rw [htag, hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hstr :
      (((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ⊢
      (∃∗ p : BitVec 64, ((r + 8#64) ↦₆₄ p) ∗ ((r + 16#64) ↦₆₄ 10#64) ∗ (p ↦ᵣ storeHookStr)) :=
    Entails.sepExists_right (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) (Entails.refl _)
  have hd : ((r + 24#64) ↦₆₄ w3) ⊢ (∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 24#64) ↦₆₄ d)) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 32#64) ↦₆₄ w4) ⊢ (∃∗ vt : BitVec 64, ((r + 32#64) ↦₆₄ vt)) :=
    Entails.sepExists_right (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) (Entails.refl _)
  have hw5 : ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 40#64) 8 :=
    pointsTo64_entails_memRegion (r + 40#64) w5
  have hpull :
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗
          ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5)) ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ w1) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
        ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ w4) ∗ ((r + 40#64) ↦₆₄ w5)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hw5)))

/-! ## 3. Session-API Model & `droppableRecordAt` Lemmas -/

theorem draws_eq_of_loadSession_eq (C : Crypto) (x : DecryptGhost)
    (ans ans' : StoreAnswers (List (BitVec 8)) Unit)
    (h : ans'.loadSession = ans.loadSession) :
    x.draws C ans' = x.draws C ans := by
  simp only [DecryptGhost.draws, loadedSession, h]

theorem model_of_save_err (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
    (ses : Session (List (BitVec 8))) (k : IdentityKey)
    (hload : ans.loadSession = .ok (some rec))
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec'))
    (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k)
    (htrust : ans.isTrustedIdentity = .ok true)
    (hsave : ans.saveIdentity = .error ()) :
    (x.model C S uuidTryParse ans).1 = .error (.store ()) ∧
      (x.model C S uuidTryParse ans).2 =
        [.loadSession x.rem.val,
          .isTrustedIdentity x.rem.val k .receiving,
          .saveIdentity x.rem.val k] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.store ()),
        [.loadSession x.rem.val,
          .isTrustedIdentity x.rem.val k .receiving,
          .saveIdentity x.rem.val k]) := by
    unfold DecryptGhost.model
    unfold decryptRecord at hdec
    rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust, hsave]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem sessionRecordAt_some_entails_droppable (A : RustAlloc) (r : BitVec 64)
    (rec' : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (hcur : rec'.currentSession = some ses) :
    (∃∗ g : RecordGhost, sessionRecordAt A r g rec') ⊢
      ∃∗ G : SessionGhost, droppableRecordAt A r (some (G, ses.state)) := by
  apply Entails.sepExists_elim
  intro ⟨prevCap, prevPtr, gcur⟩
  cases gcur with
  | none =>
    unfold sessionRecordAt
    simp only [hcur]
    rw [sepConj_comm]
    exact Entails.pure_left False.elim
  | some G =>
    refine Entails.sepExists_right G ?_
    unfold sessionRecordAt droppableRecordAt
    simp only [hcur, sessionAt_eq]
    refine sepConj_mono (Entails.sepExists_right prevCap (Entails.sepExists_right prevPtr (Entails.refl _))) ?_
    exact Entails.pure_left fun _ => Entails.refl _

/-! ## 4. Stack Splits and `messageDecrypt_call_panic` / `messageDecrypt_call_panic_p` -/

/-- Stack budget needed by `segSave_call_wp` (save shim, save poll, and `__rust_dealloc`). -/
def saveCallStack {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : Nat :=
  max ikit.saveShimStack (max ikit.savePollStack allocHookStack)

theorem saveShimStack_le_saveCall {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    ikit.saveShimStack ≤ saveCallStack ikit := Nat.le_max_left _ _

theorem savePollStack_le_saveCall {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    ikit.savePollStack ≤ saveCallStack ikit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem allocHookStack_le_saveCall {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) :
    allocHookStack ≤ saveCallStack ikit :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem saveCallStack_le_wsCalleeV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    saveCallStack ikit ≤ wsCalleeStackV kit ikit :=
  Nat.max_le.mpr ⟨saveShimStack_le_V kit ikit,
    Nat.max_le.mpr ⟨savePollStack_le_V kit ikit, allocHookStack_le_V kit ikit⟩⟩

theorem stack_saveCall_to_saveShim {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : saveCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (saveCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - ikit.saveShimStack) ∗
        stackAt sp ikit.saveShimStack :=
  stack_wsCalleeV_sub sp (saveShimStack_le_saveCall ikit) hn

theorem stack_saveShim_to_savePoll {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : saveCallStack ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - ikit.saveShimStack) ∗
        stackAt sp ikit.saveShimStack =
      memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - ikit.savePollStack) ∗
        stackAt sp ikit.savePollStack := by
  rw [← stack_saveCall_to_saveShim ikit sp hn]
  exact stack_wsCalleeV_sub sp (savePollStack_le_saveCall ikit) hn

theorem stack_savePoll_to_alloc {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : saveCallStack ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - ikit.savePollStack) ∗
        stackAt sp ikit.savePollStack =
      memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - allocHookStack) ∗
        stackAt sp allocHookStack := by
  rw [← stack_wsCalleeV_sub sp (savePollStack_le_saveCall ikit) hn]
  exact stack_wsCalleeV_sub sp (allocHookStack_le_saveCall ikit) hn

theorem stack_alloc_to_saveCall {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (sp : BitVec 64) (hn : saveCallStack ikit ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 (saveCallStack ikit))
        (saveCallStack ikit - allocHookStack) ∗
        stackAt sp allocHookStack =
      stackAt sp (saveCallStack ikit) :=
  (stack_wsCalleeV_sub sp (allocHookStack_le_saveCall ikit) hn).symm

theorem stack_wsCalleeV_saveCall {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : wsCalleeStackV kit ikit ≤ 2 ^ 64) :
    stackAt sp (wsCalleeStackV kit ikit) =
      memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - saveCallStack ikit) ∗
        stackAt sp (saveCallStack ikit) :=
  stack_wsCalleeV_sub sp (saveCallStack_le_wsCalleeV kit ikit) hn

theorem sepWPp_call_panic {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr hpre
    (fun sm code R' _ hpost => by rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm => SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm))
    (fun sm R' _ hpost => by rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

theorem sepWPp_call_panic_p {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr hpre
    (fun sm code R' _ hpost => by rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    hnext
    (fun sm R' _ hpost => by rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

theorem shim_onPanic_entails {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold allocFailedIn
  rw [htr, sepConj_assoc]
  exact sepConj_mono_right (entails_anyHeap _)

open Lean Elab Tactic in
elab "messageDecrypt_call_panic " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "messageDecrypt_call_panic_p " hcall:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p $hcall (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_p: unexpected subgoals"
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars (some hcall)
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

/-! ### `.inImage` callees (the in-image identity-store contracts, `IdentityStoreKitOkI`)

`sepWPp_call_panic_inImage` / `sepWPp_call_panic_p_inImage` call a `spec.inImage img` callee with
the image invariant passed as terms (`hfr`, `hsym`), so the precondition goal is the plain
`spec.pre`. The `_p` form also hands the continuation the invariant at the return state. The
tactics `messageDecrypt_call_panic_inImage` / `messageDecrypt_call_panic_p_inImage hcall hinv x`
(`hinv : img.FrozenLoaded s ∧ s.symtab = img.symtab` at the call state) clear every
`subroutine_ok` hypothesis and every hypothesis mentioning the image invariant from the side
goals before discharging them, so `simp … at *` never sees `Obj.Image.FrozenLoaded`. -/

theorem sepWPp_call_panic_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hfr : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  sepWPp_call_panic hcall hpc hrun hsp_align hlr
    (fun R' hm => inImage_pre_intro hfr hsym (hpre R' hm)) hpan hexit_eq hoom_eq hnext

theorem sepWPp_call_panic_p_inImage {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hfr : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf ∧ sf.symtab = img.symtab →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hfr hsym hpc hrun hsp_align hlr
    (fun R' hm => inImage_pre_intro hfr hsym (hpre R' hm))
    (fun sm code R' _ hpost => by dsimp only [Spec.inImage] at hpost; rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm hfr' hsym' => hnext sm hpcm hrunm hspm hcsm ⟨hfr', hsym'⟩)
    (fun sm R' _ hpost => by dsimp only [Spec.inImage] at hpost; rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

open Lean Elab Tactic Meta in
/-- Clear (where possible) from goal `g` every `subroutine_ok` hypothesis and every hypothesis
mentioning `Obj.Image.FrozenLoaded`, `ImgCallInv` or `FrozenInv`. -/
private meta def clearImgInvHyps (g : MVarId) : MetaM MVarId := g.withContext do
  let lastStr : Name → String := fun
    | .str _ s => s
    | _ => ""
  let mut fvs : Array FVarId := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let mentions := (ty.find? fun t => t.isConst &&
      (t.constName! == ``Arm64.Obj.Image.FrozenLoaded ||
        ["ImgCallInv", "FrozenInv"].contains (lastStr t.constName!))).isSome
    if mentions || ty.isAppOf ``Arm64.subroutine_ok then
      fvs := fvs.push decl.fvarId
  g.tryClearMany fvs

open Lean Elab Tactic in
elab "messageDecrypt_call_panic_inImage " hcall:term:max hinv:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_inImage $hcall (And.left $hinv) (And.right $hinv) (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_inImage: unexpected subgoals"
  let gPre ← clearImgInvHyps gPre
  let gPanic ← clearImgInvHyps gPanic
  let gErr ← clearImgInvHyps gErr
  let gOom ← clearImgInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
/-- `messageDecrypt_call_panic_p` for a `.inImage img` callee; the continuation also introduces
`hinv_sf : img.FrozenLoaded sf ∧ sf.symtab = img.symtab`. -/
elab "messageDecrypt_call_panic_p_inImage " hcall:term:max hinv:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hinvId ← freshIdent `hinv_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p_inImage $hcall (And.left $hinv) (And.right $hinv) (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_p_inImage: unexpected subgoals"
  let gPre ← clearImgInvHyps gPre
  let gPanic ← clearImgInvHyps gPanic
  let gErr ← clearImgInvHyps gErr
  let gOom ← clearImgInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hinvId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

def savePollTag : Except Unit IdentityChange → BitVec 64
  | .ok _ => 0xFFFFFFFFFFFFFFFE#64
  | .error () => 0x800000000000001A#64

theorem wsMeta_of_steps {prog : Program} {img : Obj.Image} {x : DecryptGhost} {s0 s sf : State}
    (hm : wsMeta img x s0 s) (hst : Steps prog s sf)
    (hrun : sf.status = .Running) (hsp : sf.sp = s.sp)
    (hx29 : sf.readReg64 .x29 = s.readReg64 .x29)
    (hx27 : sf.readReg64 .x27 = s.readReg64 .x27)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s) :
    wsMeta img x s0 sf := by
  obtain ⟨_, hsp0, hal0, hal, hx29_0, hx27_0, hfr, hsym, hvregs_0⟩ := hm
  refine ⟨hrun, hsp.trans hsp0, hal0, ?_, hx29.trans hx29_0, hx27.trans hx27_0,
    hst.frozenLoaded hfr, (hst.symtab_eq).trans hsym, hvregs.trans hvregs_0⟩
  unfold State.spAligned at hal ⊢
  rwa [hsp]

theorem allocFailedIn_trans {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem panic_outcome_of_allocFailedIn {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold withStoresDecSpecV Spec.inImage
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl (allocFailedIn_trans htr0 haf)⟩ (Entails.refl _)

def savePollOutRel (b o2 o3 o4 o5 : BitVec 64) (o1 : BitVec 32) :
    Except Unit IdentityChange → Prop
  | .ok _ => True
  | .error () =>
    o1 = (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32 ∧
    o2 = 10#32 ++ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 32 32 ∧
    o3 = 0x100000000#64 ∧
    o4 = (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 0 32 ++ 0#32 ∧
    o5.extractLsb' 0 32 = (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 32 32

@[simp] theorem savePollOutRel_ok (b o2 o3 o4 o5 : BitVec 64) (o1 : BitVec 32) (c : IdentityChange) :
    savePollOutRel b o2 o3 o4 o5 o1 (.ok c) = True := rfl

@[simp] theorem savePollOutRel_err (b w5 : BitVec 64) :
    savePollOutRel b
      (10#32 ++ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 32 32)
      4294967296#64
      ((b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 0 32 ++ 0#32)
      (w5.extractLsb' 0 32 ++ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)).extractLsb' 32 32)
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32)
      (.error ()) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact BitVec.extractLsb'_append_eq_right

/-! ## 5. Cell Split/Fold Lemmas -/

theorem bitvec64_eta32 (v : BitVec 64) :
    v.extractLsb' 32 32 ++ v.extractLsb' 0 32 = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb', Nat.zero_add]
  split_ifs with h
  · rfl
  · simp only [Nat.add_sub_of_le (Nat.not_lt.mp h)]
    rfl

theorem stagedRes_storeErr_of_savePollOutRel (A : RustAlloc)
    (b x28 w20 w21 src o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : savePollOutRel b o2 o3 o4 o5 o1 (.error ())) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  rcases hrel with ⟨ho1, ho2, ho3, ho4, ho5⟩
  refine stagedRes_storeErr_intro A b x28 w20 w21 src (o6 ++ o5.extractLsb' 32 32)
    o2 o3 o4 o5 o6 hx28 (by rw [hw1, ho1]) ho2 ho3 ho4 ?_ ?_
  · rw [BitVec.extractLsb'_append_eq_right, ← ho5, bitvec64_eta32]
  · exact BitVec.extractLsb'_append_eq_left.symm

theorem memRegion_16_entails_cells (a : BitVec 64) :
    memRegion a 0x10 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) := by
  rw [memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro c0
  exact Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.refl _))

theorem cells_16_entails_memRegion (a c0 c1 : BitVec 64) :
    ((a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1)) ⊢ memRegion a 0x10 := by
  rw [memRegion_split a 8 8 (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion a c0) (pointsTo64_entails_memRegion (a + 8#64) c1)

theorem memRegion_36_entails_cells (a : BitVec 64) :
    memRegion a 0x24 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 32,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
        ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₃₂ d4) := by
  rw [memRegion_split a 8 28 (by decide), memRegion_split (a + 8#64) 8 20 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 12 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 4 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d4; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d0
  exact Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right d2 (Entails.sepExists_right d3
      (Entails.sepExists_right d4 (Entails.refl _)))))

theorem cells_36_entails_memRegion (a d0 d1 d2 d3 : BitVec 64) (d4 : BitVec 32) :
    ((a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗
      ((a + 24#64) ↦₆₄ d3) ∗ ((a + 32#64) ↦₃₂ d4)) ⊢ memRegion a 0x24 := by
  rw [memRegion_split a 8 28 (by decide), memRegion_split (a + 8#64) 8 20 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 12 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine sepConj_mono (pointsTo64_entails_memRegion a d0) (sepConj_mono
    (pointsTo64_entails_memRegion (a + 8#64) d1) (sepConj_mono
      (pointsTo64_entails_memRegion (a + 16#64) d2) (sepConj_mono
        (pointsTo64_entails_memRegion (a + 24#64) d3)
        (pointsTo32_entails_memRegion (a + 32#64) d4))))

theorem cells_48_poll_entails_memRegion (a w0 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₃₂ o1) ∗ ((a + 12#64) ↦₆₄ o2) ∗
      ((a + 20#64) ↦₆₄ o3) ∗ ((a + 28#64) ↦₆₄ o4) ∗
      ((a + 36#64) ↦₆₄ o5) ∗ ((a + 44#64) ↦₃₂ o6)) ⊢ memRegion a 48 := by
  rw [memRegion_split a 8 40 (by decide), memRegion_split (a + 8#64) 4 36 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h36 := cells_36_entails_memRegion (a + 12#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  exact sepConj_mono (pointsTo64_entails_memRegion a w0)
    (sepConj_mono (pointsTo32_entails_memRegion (a + 8#64) o1) h36)

theorem key_entails_memRegion_32 (a : BitVec 64) (k : IdentityKey) :
    (a ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion a 0x20 := by
  have h := pointsToBytes_entails_memRegion a k.publicKey.bytes.toList
  rwa [List.Vector.toList_length] at h

theorem memRegion_300_b00_split (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0xb00 =
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        memRegion (sp + 0x5a4#64) 0x85c := by
  rw [memRegion_split (sp + 0x300#64) 0x280 0x880 (by decide),
    memRegion_split (sp + 0x300#64 + 0x280#64) 0x24 0x85c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_300_280_split (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0x280 =
      memRegion (sp + 0x520#64) 0x24 ∗
        (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) := by
  rw [memRegion_split (sp + 0x300#64) 0x220 0x60 (by decide),
    memRegion_split (sp + 0x300#64 + 0x220#64) 0x24 0x3c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

theorem memRegion_5a4_85c_split (sp : BitVec 64) :
    memRegion (sp + 0x5a4#64) 0x85c =
      memRegion (sp + 0x5f0#64) 48 ∗
        (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) := by
  rw [memRegion_split (sp + 0x5a4#64) 0x4c 0x810 (by decide),
    memRegion_split (sp + 0x5a4#64 + 0x4c#64) 48 0x7e0 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Helpers -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem stagedRes_storeErr_placed_intro (A : RustAlloc)
    (strPtr vt x28 w20 w21 src w5 o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64)
    (hw1 : resWord1 w20 w21 = strPtr.extractLsb' 0 32)
    (ho2 : o2 = (10#64 : BitVec 64).extractLsb' 0 32 ++ strPtr.extractLsb' 32 32)
    (ho3 : o3 = (1#64 : BitVec 64).extractLsb' 0 32 ++ (10#64 : BitVec 64).extractLsb' 32 32)
    (ho4 : o4 = vt.extractLsb' 0 32 ++ (1#64 : BitVec 64).extractLsb' 32 32)
    (ho5 : o5 = w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
    (ho6 : o6 = w5.extractLsb' 32 32) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      (strPtr ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  let w2 := 10#64
  let w3 := 1#64
  rw [words36At_eq_pointsToBytes]
  unfold StagedRes
  refine Entails.sepExists_right (bytes36 o2 o3 o4 o5 o6) ?_
  refine Entails.sepExists_right (strPtr ↦ᵣ storeHookStr) ?_
  refine Entails.pure_right ⟨bytes36_length o2 o3 o4 o5 o6, fun r => ?_⟩ (Entails.refl _)
  rw [hx28, hw1, ← words36At_eq_pointsToBytes]
  have hrep := (out_repack r strPtr w2 w3 vt w5).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep ⊢
  have hgrp :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₃₂ strPtr.extractLsb' 0 32) ∗
        (((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₃₂ strPtr.extractLsb' 0 32) ∗
          ((r + 12#64) ↦₆₄ o2) ∗ ((r + 20#64) ↦₆₄ o3) ∗ ((r + 28#64) ↦₆₄ o4) ∗
          ((r + 36#64) ↦₆₄ o5) ∗ ((r + 44#64) ↦₃₂ o6)) ∗
        (strPtr ↦ᵣ storeHookStr)) := by ac_rfl
  rw [hgrp, ho2, ho3, ho4, ho5, ho6, hrep]
  unfold apiDecResultAt apiErrAt strRefAt
  have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by decide +kernel
  have htag : (0x800000000000001A#64 : BitVec 64) = speWord speApplicationCallback := rfl
  rw [htag, hlen]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hstr :
      (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ (strPtr ↦ᵣ storeHookStr)) ⊢
      (∃∗ p : BitVec 64, ((r + 8#64) ↦₆₄ p) ∗ ((r + 16#64) ↦₆₄ 10#64) ∗ (p ↦ᵣ storeHookStr)) :=
    Entails.sepExists_right strPtr (Entails.refl _)
  have hd : ((r + 24#64) ↦₆₄ w3) ⊢ (∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 24#64) ↦₆₄ d)) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 32#64) ↦₆₄ vt) ⊢ (∃∗ vt' : BitVec 64, ((r + 32#64) ↦₆₄ vt')) :=
    Entails.sepExists_right vt (Entails.refl _)
  have hw5 : ((r + 40#64) ↦₆₄ w5) ⊢ memRegion (r + 40#64) 8 :=
    pointsTo64_entails_memRegion (r + 40#64) w5
  have hpull :
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ ((r + 24#64) ↦₆₄ w3) ∗
          ((r + 32#64) ↦₆₄ vt) ∗ ((r + 40#64) ↦₆₄ w5)) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ speWord speApplicationCallback) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 16#64) ↦₆₄ w2) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
        ((r + 24#64) ↦₆₄ w3) ∗ ((r + 32#64) ↦₆₄ vt) ∗ ((r + 40#64) ↦₆₄ w5)) := by ac_rfl
  rw [hpull]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hw5)))

def pollOutPlacedRel {α : Type} (strPtr vt o2 o3 o4 o5 : BitVec 64) (o1 : BitVec 32) :
    Except Unit α → Prop
  | .ok _ => True
  | .error () =>
    o1 = strPtr.extractLsb' 0 32 ∧
    o2 = 10#32 ++ strPtr.extractLsb' 32 32 ∧
    o3 = 0x100000000#64 ∧
    o4 = vt.extractLsb' 0 32 ++ 0#32 ∧
    o5.extractLsb' 0 32 = vt.extractLsb' 32 32

@[simp] theorem pollOutPlacedRel_ok {α : Type} (strPtr vt o2 o3 o4 o5 : BitVec 64)
    (o1 : BitVec 32) (c : α) :
    pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 (.ok c) = True := rfl

@[simp] theorem pollOutPlacedRel_err {α : Type} (strPtr vt w5 : BitVec 64) :
    pollOutPlacedRel (α := α) strPtr vt
      (10#32 ++ strPtr.extractLsb' 32 32)
      4294967296#64
      (vt.extractLsb' 0 32 ++ 0#32)
      (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (strPtr.extractLsb' 0 32)
      (.error ()) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact BitVec.extractLsb'_append_eq_right

theorem stagedRes_storeErr_of_pollOutPlacedRel {α : Type} (A : RustAlloc)
    (strPtr vt x28 w20 w21 src o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := α) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    ((src ↦₆₄ o2) ∗ ((src + 8#64) ↦₆₄ o3) ∗ ((src + 16#64) ↦₆₄ o4) ∗
      ((src + 24#64) ↦₆₄ o5) ∗ ((src + 32#64) ↦₃₂ o6)) ∗
      (strPtr ↦ᵣ storeHookStr) ⊢
      StagedRes A x28 w20 w21 src (.error (.store ())) := by
  rcases hrel with ⟨ho1, ho2, ho3, ho4, ho5⟩
  refine stagedRes_storeErr_placed_intro A strPtr vt x28 w20 w21 src (o6 ++ o5.extractLsb' 32 32)
    o2 o3 o4 o5 o6 hx28 (by rw [hw1, ho1]) ho2 ho3 ho4 ?_ ?_
  · rw [BitVec.extractLsb'_append_eq_right, ← ho5, bitvec64_eta32]
  · exact BitVec.extractLsb'_append_eq_left.symm

def withLsRoClBox {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  StoreKit.withLsRoCl pl spec

theorem box_lscro {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec)) :
    subroutine_ok prog entry (withLsRoClBox pl spec) := h

theorem subroutine_ok_withStepsPost_lscro {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (StoreKit.withLsRoCl pl spec)) :
    subroutine_ok prog entry (withLsRoClBox pl (withStepsPost prog spec)) := by
  show subroutine_ok prog entry (StoreKit.withLsRoCl pl (withStepsPost prog spec))
  refine subroutine_ok_mono (subroutine_ok_withStepsPost h)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_) (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  dsimp only [StoreKit.withLsRoCl, withStepsPost, Arm64.ReachesOutcome.withStepsPost] at hq ⊢
  exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hq

theorem shim_197 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {off : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok (lsProg_197 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl spec)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) off
      (withLsRoClBox lsmpl (withStepsPost ((blkPC_197).rebase (blkPl_197).base H) spec)) := by
  rw [BitVec.zero_add] at h
  exact subroutine_ok_withStepsPost_lscro h

theorem box_lscro_197 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {off : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok (lsProg_197 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl spec)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) off (withLsRoClBox lsmpl spec) := by
  rw [BitVec.zero_add] at h
  exact h

theorem futDrop_197 [LibsignalPlacement] {H : LibsignalHooks} {off : BitVec 64}
    (h : subroutine_ok (lsProg_197 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl futDropSpec)) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) off
      (StoreKit.withLsCodeRoLoaded lsmpl futDropSpec) := by
  rw [BitVec.zero_add] at h
  exact StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl h

theorem lscro_pre_intro {α : Type} {pl : Obj.MultiPlacement} {spec : Spec α}
    {x : α} {s0 : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded pl s0.mem)
    (h : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsRoClBox pl spec).pre x s0 ∗ R := by
  dsimp only [withLsRoClBox, StoreKit.withLsRoCl]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcrl, h⟩

theorem sepWPp_call_panic_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsRoClBox lsmpl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWP prog target_pc sf (spec.post x s sf ∗ F) post) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => lscro_pre_intro hcrl (hpre R' hm))
    (fun sm code R' _ hpost => by dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hpost; rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm => by
      dsimp only [withLsRoClBox, StoreKit.withLsRoCl]; rw [sepConj_assoc]
      exact SepWPp.pure_elim fun hcrl_sm => SepWPp.of_sepWP_ret (hnext sm hpcm hrunm hspm hcsm hcrl_sm))
    (fun sm R' _ hpost => by dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hpost; rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

theorem sepWPp_call_panic_p_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsRoClBox lsmpl spec))
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) :=
  ProofLib.SepWPp.call_wpp (x := x) (F := F) hcall hpc hrun hsp_align hlr
    (fun R' hm => lscro_pre_intro hcrl (hpre R' hm))
    (fun sm code R' _ hpost => by dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hpost; rw [hexit_eq] at hpost; exact not_satisfies_false_sepConj hpost)
    (fun sm _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm')
    (fun sm hpcm hrunm hspm hcsm => by
      dsimp only [withLsRoClBox, StoreKit.withLsRoCl]; rw [sepConj_assoc]
      exact SepWPp.pure_elim fun hcrl_sm => hnext sm hpcm hrunm hspm hcsm hcrl_sm)
    (fun sm R' _ hpost => by dsimp only [withLsRoClBox, StoreKit.withLsRoCl] at hpost; rw [hoom_eq] at hpost; exact (not_satisfies_false_sepConj hpost).elim)

open Lean Elab Tactic Meta in
meta def clearLscroInvHyps (g : MVarId) : MetaM MVarId := g.withContext do
  let lastStr : Name → String := fun
    | .str _ s => s
    | _ => ""
  let mut fvs : Array FVarId := #[]
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    let mentions := (ty.find? fun t => t.isConst &&
      (["LibsignalCodeRoLoaded", "LibsignalCodeLoaded", "LibsignalRoLoaded"].contains
        (lastStr t.constName!))).isSome
    if mentions || ty.isAppOf ``Arm64.subroutine_ok then
      fvs := fvs.push decl.fvarId
  g.tryClearMany fvs

open Lean Elab Tactic in
elab "messageDecrypt_call_panic_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId := mkIdent `hcrl_poll
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
elab "messageDecrypt_call_panic_p_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId ← freshIdent `hcrl_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "messageDecrypt_call_panic_p_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId

theorem wsMetaPlaced_of_steps [LibsignalPlacement] {prog : Program} {x : DecryptGhost} {s0 s sf : State}
    (hm : wsMetaPlaced x s0 s) (hst : Steps prog s sf)
    (hrun : sf.status = .Running) (hsp : sf.sp = s.sp)
    (hx29 : sf.readReg64 .x29 = s.readReg64 .x29)
    (hx27 : sf.readReg64 .x27 = s.readReg64 .x27)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s) :
    wsMetaPlaced x s0 sf := by
  obtain ⟨_, hsp0, hal0, hal, hx29_0, hx27_0, hcrl, hvregs_0⟩ := hm
  refine ⟨hrun, hsp.trans hsp0, hal0, ?_, hx29.trans hx29_0, hx27.trans hx27_0,
    hcrl.of_keepsFrozen hst.keepsFrozen, hvregs.trans hvregs_0⟩
  unfold State.spAligned at hal ⊢
  rwa [hsp]

theorem panic_outcome_of_allocFailedInVPlaced [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold withStoresDecPlacedSpecV StoreKit.withLsCodeRoLoaded
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl (allocFailedIn_trans htr0 haf)⟩ (Entails.refl _)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
