/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.RecordMove
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.RoDataReloc -- shake: keep
import LibsignalBinary.Proofs.Common.StringCloneFlat
import LibsignalBinary.Proofs.Common.StringClonePlaced

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Instruction decode lemmas (`0x3a534:3`, `0x3a580:52`, `0x3a950:20`, `0x3c7b4:7`) -/

gen_decodes libsignalSessionCode_tree messageDecryptDispatchBin [(ls_off% "session_message_decrypt_signal" + 140) → (ls_off% "session_message_decrypt_signal" + 148), (ls_off% "session_message_decrypt_signal" + 216) → (ls_off% "session_message_decrypt_signal" + 420),
    (ls_off% "session_message_decrypt_signal" + 1192) → (ls_off% "session_message_decrypt_signal" + 1268), (ls_off% "session_message_decrypt_signal" + 8972) → (ls_off% "session_message_decrypt_signal" + 8996)]

/-! ## 2. Record and memory helper lemmas -/

theorem recordSplit_ok : RecordSplit := by
  intro A r g rec s G hcur hg
  unfold sessionRecordAt prevBufAt vecAt vecHeader
  rw [hcur, hg]
  dsimp only [List.length, BitVec.ofNat]
  rw [sessionAt_eq]
  exact Entails.of_eq (by ac_nf)

theorem recordNone_split (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (hcur : rec.currentSession = none) :
    sessionRecordAt A r g rec ⊢
      (r ↦₆₄ g.prevCap) ∗ prevBufAt A g.prevCap g.prevPtr ∗
        ((r + 8#64) ↦₆₄ g.prevPtr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
        ((r + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (r + 0x20#64) 336 := by
  unfold sessionRecordAt prevBufAt vecAt vecHeader
  rw [hcur]
  dsimp only [List.length, BitVec.ofNat]
  cases g.cur with
  | none =>
    dsimp only []
    exact Entails.of_eq (by ac_nf)
  | some G =>
    dsimp only []
    rw [sepConj_comm]
    exact Entails.pure_left (fun hF => False.elim hF)

theorem rootStack_le_sp {s0 s : State} (hsp : s.sp = s0.sp - 0xee0#64)
    (hle : wsStack ≤ s0.sp.toNat) : rootStack ≤ s.sp.toNat := by
  unfold wsStack entryStack at hle
  unfold rootStack
  rw [hsp]
  bv_omega

def q0Lo (w2 w3 : BitVec 64) : BitVec 64 := w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32
def q0Hi (w3 w4 : BitVec 64) : BitVec 64 := w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32
def q1Lo (w4 w5 : BitVec 64) : BitVec 64 := w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32
def q1Hi (w5 w6 : BitVec 64) : BitVec 64 := w6.extractLsb' 0 32 ++ w5.extractLsb' 32 32

def q0OfWords (w2 w3 w4 : BitVec 64) : BitVec 128 := q0Hi w3 w4 ++ q0Lo w2 w3
def q1OfWords (w4 w5 w6 : BitVec 64) : BitVec 128 := q1Hi w5 w6 ++ q1Lo w4 w5

theorem recordWords56At_repack (p w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    recordWords56At p w0 w1 w2 w3 w4 w5 w6 =
      (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗
        ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((p + 0x14#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((p + 0x24#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((p + 0x34#64) ↦₃₂ w6.extractLsb' 32 32) := by
  unfold recordWords56At q0OfWords q1OfWords q0Lo q0Hi q1Lo q1Hi
  have hpull :
      ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 0x10#64) ↦₆₄ w2) ∗
        ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
        ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6)) =
      ((p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗
        (((p + 0x10#64) ↦₆₄ w2) ∗ ((p + 0x18#64) ↦₆₄ w3) ∗ ((p + 0x20#64) ↦₆₄ w4) ∗
          ((p + 0x28#64) ↦₆₄ w5) ∗ ((p + 0x30#64) ↦₆₄ w6))) := by ac_rfl
  rw [hpull, words5_repack_w32_2q128_w32 p w2 w3 w4 w5 w6]

theorem resWord1_lsr8 (w : BitVec 32) :
    resWord1
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 w >>> 8)))
      (BitVec.zeroExtend 64 w) = w := by
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

theorem pointsToBytes_36_q128_eq (a : BitVec 64) (u0 u1 u2 u3 : BitVec 64) (u4 : BitVec 32) :
    ((a ↦₁₂₈ (u1 ++ u0)) ∗ ((a + 0x10#64) ↦₁₂₈ (u3 ++ u2)) ∗ ((a + 0x20#64) ↦₃₂ u4)) =
      (a ↦ₛ (unpack64 u0 ++ unpack64 u1 ++ unpack64 u2 ++ unpack64 u3 ++ unpack32 u4)) := by
  rw [← pointsTo64_pair a u0 u1, ← pointsTo64_pair (a + 0x10#64) u2 u3]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem stagedRes_of_words5 (A : RustAlloc) (src x28 w2 w3 w4 w5 w6 : BitVec 64)
    (F : SepProp) (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (h : ∀ r : BitVec 64,
      ((r ↦₆₄ x28) ∗ ((r + 8#64) ↦₆₄ w2) ∗ ((r + 0x10#64) ↦₆₄ w3) ∗
        ((r + 0x18#64) ↦₆₄ w4) ∗ ((r + 0x20#64) ↦₆₄ w5) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗ F) ⊢
        apiDecResultAt A r res) :
    (((src ↦₁₂₈ q0OfWords w2 w3 w4) ∗ ((src + 0x10#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
      ((src + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗ F) ⊢
      StagedRes A x28
        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (w2.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (w2.extractLsb' 0 32)) src res := by
  unfold StagedRes q0OfWords q1OfWords
  rw [pointsToBytes_36_q128_eq]
  refine Entails.sepExists_right
    (unpack64 (q0Lo w2 w3) ++ unpack64 (q0Hi w3 w4) ++
      unpack64 (q1Lo w4 w5) ++ unpack64 (q1Hi w5 w6) ++ unpack32 (w6.extractLsb' 32 32))
    (Entails.sepExists_right F ?_)
  refine Entails.pure_right ⟨by simp, ?_⟩ (Entails.refl _)
  intro r
  rw [resWord1_lsr8, ← pointsToBytes_36_q128_eq]
  have hr :
      ((r + 8#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((r + 12#64) ↦₁₂₈ (q0Hi w3 w4 ++ q0Lo w2 w3)) ∗
        ((r + 12#64 + 0x10#64) ↦₁₂₈ (q1Hi w5 w6 ++ q1Lo w4 w5)) ∗
        ((r + 12#64 + 0x20#64) ↦₃₂ w6.extractLsb' 32 32) =
      ((r + 8#64) ↦₆₄ w2) ∗ ((r + 0x10#64) ↦₆₄ w3) ∗ ((r + 0x18#64) ↦₆₄ w4) ∗
        ((r + 0x20#64) ↦₆₄ w5) ∗ ((r + 0x28#64) ↦₆₄ w6) := by
    have hrep := (words5_repack_w32_2q128_w32 (r - 8#64) w2 w3 w4 w5 w6).symm
    have h08 : r - 8#64 + 0x10#64 = r + 8#64 := by bv_arith
    have h0c : r - 8#64 + 0x14#64 = r + 12#64 := by bv_arith
    have h1c : r - 8#64 + 0x24#64 = r + 12#64 + 0x10#64 := by bv_arith
    have h2c : r - 8#64 + 0x34#64 = r + 12#64 + 0x20#64 := by bv_arith
    have h10 : r - 8#64 + 0x18#64 = r + 0x10#64 := by bv_arith
    have h18 : r - 8#64 + 0x20#64 = r + 0x18#64 := by bv_arith
    have h20 : r - 8#64 + 0x28#64 = r + 0x20#64 := by bv_arith
    have h28 : r - 8#64 + 0x30#64 = r + 0x28#64 := by bv_arith
    unfold q0Lo q0Hi q1Lo q1Hi
    rw [h08, h0c, h1c, h2c, h10, h18, h20, h28] at hrep
    exact hrep
  have hrearrange :
      ((r ↦₆₄ x28) ∗ ((r + 8#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        (((r + 12#64) ↦₁₂₈ (q0Hi w3 w4 ++ q0Lo w2 w3)) ∗
          ((r + 12#64 + 0x10#64) ↦₁₂₈ (q1Hi w5 w6 ++ q1Lo w4 w5)) ∗
          ((r + 12#64 + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗ F) =
      ((r ↦₆₄ x28) ∗
        (((r + 8#64) ↦₃₂ w2.extractLsb' 0 32) ∗
          ((r + 12#64) ↦₁₂₈ (q0Hi w3 w4 ++ q0Lo w2 w3)) ∗
          ((r + 12#64 + 0x10#64) ↦₁₂₈ (q1Hi w5 w6 ++ q1Lo w4 w5)) ∗
          ((r + 12#64 + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗ F) := by ac_rfl
  rw [hrearrange, hr]
  exact Entails.trans (Entails.of_eq (by ac_nf)) (h r)

theorem pointsTo64_of_cons_unpack64 (q : BitVec 64) (b0 : BitVec 8) (pad : List (BitVec 8))
    (w4 : BitVec 64) (hw4 : b0 :: pad = unpack64 w4) :
    ((q ↦₈ b0) ∗ ((q + 1#64) ↦ₛ pad)) = (q ↦₆₄ w4) := by
  rw [pointsTo64_eq_pointsToBytes, ← hw4, pointsToBytes_cons]

theorem pointsTo64_entails_byte_memRegion7 (q : BitVec 64) (b0 : BitVec 8) (pad : List (BitVec 8))
    (w4 : BitVec 64) (hpad : pad.length = 7) (hw4 : b0 :: pad = unpack64 w4) :
    (q ↦₆₄ w4) ⊢ (q ↦₈ b0) ∗ memRegion (q + 1#64) 7 := by
  rw [← pointsTo64_of_cons_unpack64 q b0 pad w4 hw4]
  apply sepConj_mono_right
  have h := pointsToBytes_entails_memRegion (q + 1#64) pad
  rwa [hpad] at h

open ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoProofLib.RoDataReloc in
theorem img_dataLen : libsignalSessionImage.data.length = num% (ls_field% dataLen) := by rfl_kernel

set_option maxRecDepth 200000 in
open ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux CryptoProofLib.RoDataReloc in
theorem Satisfies.of_rodata_bytes' {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    {off : Nat} {bs : List (BitVec 8)}
    (h : (decide (libsignalSessionImage.dataOff ≤ off) &&
      decide ((off - libsignalSessionImage.dataOff) + bs.length ≤ num% (ls_field% dataLen)) &&
      noRelocInRange libsignalSessionImage.relocs
        (num% (ls_field% dataLen) + libsignalSessionImage.bss)
        (off - libsignalSessionImage.dataOff) bs.length &&
      inLiRoData libsignalSessionImage off bs.length &&
      decide ((libsignalSessionImage.data.drop (off - libsignalSessionImage.dataOff)).take bs.length = bs)) = true)
    (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦ᵣ bs) ∗ P := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hk : (off - libsignalSessionImage.dataOff) + bs.length ≤ libsignalSessionImage.data.length := by
    rw [img_dataLen]; exact h.1.1.1.2
  have hno : noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss)
      (off - libsignalSessionImage.dataOff) bs.length = true := by
    rw [img_dataLen]; exact h.1.1.2
  have hholds := loads_rodata_holdsBytes himg hF h.1.1.1.1 hk hno h.1.2 rfl h.2
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hholds
  exact Satisfies.rodata_intro hRO hread (by omega) hP

set_option maxRecDepth 200000 in
theorem satisfies_rodata_msgDecryptStr {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal") ∗ P :=
  Satisfies.of_rodata_bytes' himg hF (off := num% (ls_xref% 0x3aa44 0x3aa48)) (bs := utf8 "message_decrypt_signal")
    (by rfl_kernel) hP

theorem strRefAt_intro (a p : BitVec 64) (s : List (BitVec 8)) :
    (a ↦₆₄ p) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 s.length) ∗ (p ↦ᵣ s) ⊢ strRefAt a s :=
  Entails.sepExists_right p (Entails.refl _)

theorem apiDecResultAt_store_of_words (A : RustAlloc) (b w6 r : BitVec 64) :
    ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
      ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ⊢
      apiDecResultAt A r (.error (.store ())) := by
  dsimp only [apiDecResultAt, apiErrAt]
  have hspe : speWord speApplicationCallback = 0x800000000000001A#64 := rfl
  have hstr : (((r + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ⊢
      strRefAt (r + 8#64) storeHookStr := by
    have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by rfl_kernel
    have h10 : r + 8#64 + 8#64 = r + 0x10#64 := by bv_arith
    have h := strRefAt_intro (r + 8#64) (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) storeHookStr
    rwa [hlen, h10] at h
  have hd : ((r + 0x18#64) ↦₆₄ 1#64) ⊢ ∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 0x18#64) ↦₆₄ d) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ⊢ ∃∗ vt : BitVec 64, ((r + 0x20#64) ↦₆₄ vt) :=
    Entails.sepExists_right (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) (Entails.refl _)
  have hm8 : ((r + 0x28#64) ↦₆₄ w6) ⊢ memRegion (r + 0x28#64) 8 := by
    rw [ProofLib.memRegion_eight]
    exact Entails.sepExists_right w6 (Entails.refl _)
  rw [hspe]
  have hreord :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
        ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
        ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₆₄ (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))) ∗
          ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ∗
        ((r + 0x18#64) ↦₆₄ 1#64) ∗ ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))) ∗
        ((r + 0x28#64) ↦₆₄ w6)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hm8)))

theorem stagedRes_store_err (A : RustAlloc) (src b w6 : BitVec 64) :
    (((src ↦₁₂₈ q0OfWords (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) 10#64 1#64) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords 1#64 (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) w6) ∗
      ((src + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)) ⊢
      StagedRes A 0x800000000000001A#64
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))).extractLsb' 0 32))
        src (.error (.store ())) :=
  stagedRes_of_words5 A src 0x800000000000001A#64 (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) 10#64 1#64
    (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) w6 ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) (.error (.store ()))
    (apiDecResultAt_store_of_words A b w6)

theorem vecU8_intro (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader vecU8Buf
  exact Entails.of_eq (by simp only [sepConj_assoc])

theorem apiDecResultAt_sessionNotFound_of_words (A : RustAlloc) (a : AddrVal)
    (cap ptr b w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) (r : BitVec 64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
      ((r + 0x18#64) ↦₆₄ w4) ∗
      ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3aa44 0x3aa48))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      apiDecResultAt A r (.error (.sessionNotFound a "message_decrypt_signal")) := by
  dsimp only [apiDecResultAt, apiErrAt, addrCloneAt]
  have hvec := vecU8_intro A r cap ptr a.name
  have hw4_ent := pointsTo64_entails_byte_memRegion7 (r + 0x18#64) a.device pad w4 hpad hw4
  have h19 : r + 0x18#64 + 1#64 = r + 0x19#64 := by bv_arith
  rw [h19] at hw4_ent
  have hstr : (((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3aa44 0x3aa48))) ∗
      ((r + 0x28#64) ↦₆₄ 22#64) ∗ ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal")) ⊢
      strRefAt (r + 0x20#64) (utf8 "message_decrypt_signal") := by
    have hlen : BitVec.ofNat 64 (utf8 "message_decrypt_signal").length = 22#64 := by rfl_kernel
    have h28 : r + 0x20#64 + 8#64 = r + 0x28#64 := by bv_arith
    have h := strRefAt_intro (r + 0x20#64) (b + bv% (ls_xref% 0x3aa44 0x3aa48)) (utf8 "message_decrypt_signal")
    rwa [hlen, h28] at h
  have hreord :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
        ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((r + 0x18#64) ↦₆₄ w4) ∗
        ((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3aa44 0x3aa48))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
        (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal"))) =
      ((((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
          ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((r + 0x18#64) ↦₆₄ w4)) ∗
        (((r + 0x20#64) ↦₆₄ (b + bv% (ls_xref% 0x3aa44 0x3aa48))) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
          ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal"))) := by ac_rfl
  rw [hreord]
  exact sepConj_mono (sepConj_mono hvec hw4_ent) hstr

theorem stagedRes_sessionNotFound (A : RustAlloc) (src : BitVec 64) (a : AddrVal)
    (cap ptr b w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) :
    (((src ↦₁₂₈ q0OfWords ptr (BitVec.ofNat 64 a.name.length) w4) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords w4 (b + bv% (ls_xref% 0x3aa44 0x3aa48)) 22#64) ∗
      ((src + 0x20#64) ↦₃₂ 0#32)) ∗
      (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      StagedRes A cap
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32))
        src (.error (.sessionNotFound a "message_decrypt_signal")) := by
  have h22 : (22#64 : BitVec 64).extractLsb' 32 32 = 0#32 := rfl
  rw [← h22]
  exact stagedRes_of_words5 A src cap ptr (BitVec.ofNat 64 a.name.length) w4
    (b + bv% (ls_xref% 0x3aa44 0x3aa48)) 22#64
    (vecU8Buf A cap ptr a.name ∗ ((b + bv% (ls_xref% 0x3aa44 0x3aa48)) ↦ᵣ utf8 "message_decrypt_signal"))
    (.error (.sessionNotFound a "message_decrypt_signal"))
    (apiDecResultAt_sessionNotFound_of_words A a cap ptr b w4 pad hpad hw4)

/-! ## 3. Stack and frame `memRegion` split / join helpers -/

theorem stack_wsCallee_dealloc (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      stackAt sp allocHookStack ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - allocHookStack) := by
  have h := ProofLib.stackAt_split_bottom sp allocHookStack (wsCalleeStack - allocHookStack) (by decide)
  rw [show allocHookStack + (wsCalleeStack - allocHookStack) = wsCalleeStack by decide] at h
  rw [h, sepConj_comm]

theorem stack_wsCallee_dealloc_back (sp : BitVec 64) :
    stackAt sp allocHookStack ∗
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - allocHookStack) =
      stackAt sp wsCalleeStack :=
  (stack_wsCallee_dealloc sp).symm

theorem stack_wsCallee_ext (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      stackAt sp extHookStack ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - extHookStack) := by
  have h := ProofLib.stackAt_split_bottom sp extHookStack (wsCalleeStack - extHookStack) (by decide)
  rw [show extHookStack + (wsCalleeStack - extHookStack) = wsCalleeStack by decide] at h
  rw [h, sepConj_comm]

theorem stack_wsCallee_ext_back (sp : BitVec 64) :
    stackAt sp extHookStack ∗
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - extHookStack) =
      stackAt sp wsCalleeStack :=
  (stack_wsCallee_ext sp).symm

theorem stack_wsCallee_root (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      stackAt sp rootStack ∗
        memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) := by
  have h := ProofLib.stackAt_split_bottom sp rootStack (wsCalleeStack - rootStack) (by decide)
  rw [show rootStack + (wsCalleeStack - rootStack) = wsCalleeStack by decide] at h
  rw [h, sepConj_comm]

theorem fold_2d0 (sp w0 w1 : BitVec 64) :
    ((sp + 0x2d0#64) ↦₆₄ w0) ∗ ((sp + 0x2d8#64) ↦₆₄ w1) ⊢
      memRegion (sp + 0x2d0#64) 0x10 := by
  rw [memRegion_split (sp + 0x2d0#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ProofLib.memRegion_eight]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (Entails.sepExists_right w1 (Entails.refl _))

theorem fold_box24 (box w0 w1 : BitVec 64) (b2 : BitVec 8) :
    (box ↦₆₄ w0) ∗ ((box + 8#64) ↦₆₄ w1) ∗ ((box + 0x10#64) ↦₈ b2) ∗
      memRegion (box + 0x11#64) 7 ⊢ memRegion box 24 := by
  rw [memRegion_split box 8 16 (by decide),
      memRegion_split (box + 8#64) 8 8 (by decide),
      memRegion_split (box + 8#64 + 8#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_one]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right b2 (Entails.refl _))))

theorem split_300_for_recordMove (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0x1b0 =
      memRegion (sp + 0x300#64) 0x28 ∗
      memRegion (sp + 0x328#64) 312 ∗
      (∃∗ q0 : BitVec 128, ((sp + 0x460#64) ↦₁₂₈ q0)) ∗
      (∃∗ q1 : BitVec 128, ((sp + 0x470#64) ↦₁₂₈ q1)) ∗
      (∃∗ w8 : BitVec 32, ((sp + 0x480#64) ↦₃₂ w8)) ∗
      memRegion (sp + 0x484#64) 0x2c := by
  rw [memRegion_split (sp + 0x300#64) 0x28 0x188 (by decide),
      memRegion_split (sp + 0x300#64 + 0x28#64) 312 0x50 (by decide),
      memRegion_split (sp + 0x300#64 + 0x28#64 + 312#64) 16 0x40 (by decide),
      memRegion_split (sp + 0x300#64 + 0x28#64 + 312#64 + 16#64) 16 0x30 (by decide),
      memRegion_split (sp + 0x300#64 + 0x28#64 + 312#64 + 16#64 + 16#64) 4 0x2c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    memRegion_16_eq_exists_pointsTo128, ProofLib.memRegion_four]

theorem fold_300_after_some (sp : BitVec 64) (q0 q1 : BitVec 128) (w8 : BitVec 32) :
    memRegion (sp + 0x300#64) 0x28 ∗
      memRegion (sp + 0x328#64) 312 ∗
      ((sp + 0x460#64) ↦₁₂₈ q0) ∗
      ((sp + 0x470#64) ↦₁₂₈ q1) ∗
      ((sp + 0x480#64) ↦₃₂ w8) ∗
      memRegion (sp + 0x484#64) 0x2c ⊢
      memRegion (sp + 0x300#64) 0x1b0 := by
  rw [split_300_for_recordMove sp]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  exact sepConj_mono (Entails.sepExists_right q0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right q1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right w8 (Entails.refl _))))

theorem split_120_for_some (sp : BitVec 64) :
    memRegion (sp + 0x120#64) 0x1a8 =
      (∃∗ w0 : BitVec 64, ((sp + 0x120#64) ↦₆₄ w0)) ∗
      (∃∗ w1 : BitVec 64, ((sp + 0x128#64) ↦₆₄ w1)) ∗
      (∃∗ w2 : BitVec 32, ((sp + 0x130#64) ↦₃₂ w2)) ∗
      (∃∗ q0 : BitVec 128, ((sp + 0x134#64) ↦₁₂₈ q0)) ∗
      (∃∗ q1 : BitVec 128, ((sp + 0x144#64) ↦₁₂₈ q1)) ∗
      (∃∗ w8 : BitVec 32, ((sp + 0x154#64) ↦₃₂ w8)) ∗
      memRegion (sp + 0x158#64) 312 ∗
      memRegion (sp + 0x290#64) 0x38 := by
  rw [memRegion_split (sp + 0x120#64) 8 0x1a0 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64) 8 0x198 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64 + 8#64) 4 0x194 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 4#64) 16 0x184 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 4#64 + 16#64) 16 0x174 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 4#64 + 16#64 + 16#64) 4 0x170 (by decide),
      memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 4#64 + 16#64 + 16#64 + 4#64) 312 0x38 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four, memRegion_16_eq_exists_pointsTo128]

theorem join_4b0_5f0_760 (sp : BitVec 64) :
    memRegion (sp + 0x4b0#64) 0x140 ∗
      memRegion (sp + 0x5f0#64) 368 ∗
      memRegion (sp + 0x760#64) 0x6a0 =
      memRegion (sp + 0x4b0#64) 0x950 := by
  rw [memRegion_split (sp + 0x4b0#64) 0x140 0x810 (by decide),
      memRegion_split (sp + 0x4b0#64 + 0x140#64) 368 0x6a0 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem split_300_for_resultCopy (sp : BitVec 64) :
    memRegion (sp + 0x300#64) 0x28 =
      (∃∗ q0 : BitVec 128, ((sp + 0x300#64) ↦₁₂₈ q0)) ∗
      (∃∗ q1 : BitVec 128, ((sp + 0x310#64) ↦₁₂₈ q1)) ∗
      (∃∗ w8 : BitVec 32, ((sp + 0x320#64) ↦₃₂ w8)) ∗
      memRegion (sp + 0x324#64) 4 := by
  rw [memRegion_split (sp + 0x300#64) 16 24 (by decide),
      memRegion_split (sp + 0x300#64 + 16#64) 16 8 (by decide),
      memRegion_split (sp + 0x300#64 + 16#64 + 16#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    memRegion_16_eq_exists_pointsTo128, ProofLib.memRegion_four]

theorem split_4b0_for_resultCopy (sp : BitVec 64) :
    memRegion (sp + 0x4b0#64) 0x140 =
      memRegion (sp + 0x4b0#64) 0xd0 ∗
      (∃∗ q0 : BitVec 128, ((sp + 0x580#64) ↦₁₂₈ q0)) ∗
      (∃∗ q1 : BitVec 128, ((sp + 0x590#64) ↦₁₂₈ q1)) ∗
      (∃∗ w8 : BitVec 32, ((sp + 0x5a0#64) ↦₃₂ w8)) ∗
      memRegion (sp + 0x5a4#64) 0x4c := by
  rw [memRegion_split (sp + 0x4b0#64) 0xd0 0x70 (by decide),
      memRegion_split (sp + 0x4b0#64 + 0xd0#64) 16 0x60 (by decide),
      memRegion_split (sp + 0x4b0#64 + 0xd0#64 + 16#64) 16 0x50 (by decide),
      memRegion_split (sp + 0x4b0#64 + 0xd0#64 + 16#64 + 16#64) 4 0x4c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    memRegion_16_eq_exists_pointsTo128, ProofLib.memRegion_four]

theorem fold_4b0_after_resultCopy (sp : BitVec 64) (q0 q1 : BitVec 128) (w8 : BitVec 32) :
    memRegion (sp + 0x4b0#64) 0xd0 ∗
      ((sp + 0x580#64) ↦₁₂₈ q0) ∗
      ((sp + 0x590#64) ↦₁₂₈ q1) ∗
      ((sp + 0x5a0#64) ↦₃₂ w8) ∗
      memRegion (sp + 0x5a4#64) 0x4c ⊢
      memRegion (sp + 0x4b0#64) 0x140 := by
  rw [split_4b0_for_resultCopy sp]
  refine sepConj_mono_right ?_
  exact sepConj_mono (Entails.sepExists_right q0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right q1 (Entails.refl _))
      (sepConj_mono_left (Entails.sepExists_right w8 (Entails.refl _))))

theorem fold_328_after_recordMove (sp : BitVec 64) (tail : List (BitVec 8)) (htail : tail.length = 312)
    (q0 q1 : BitVec 128) (w8 : BitVec 32) :
    ((sp + 0x328#64) ↦ₛ tail) ∗
      ((sp + 0x460#64) ↦₁₂₈ q0) ∗
      ((sp + 0x470#64) ↦₁₂₈ q1) ∗
      ((sp + 0x480#64) ↦₃₂ w8) ∗
      memRegion (sp + 0x484#64) 0x2c ⊢
      memRegion (sp + 0x328#64) 0x188 := by
  rw [memRegion_split (sp + 0x328#64) 312 0x50 (by decide),
      memRegion_split (sp + 0x328#64 + 312#64) 16 0x40 (by decide),
      memRegion_split (sp + 0x328#64 + 312#64 + 16#64) 16 0x30 (by decide),
      memRegion_split (sp + 0x328#64 + 312#64 + 16#64 + 16#64) 4 0x2c (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    memRegion_16_eq_exists_pointsTo128, ProofLib.memRegion_four]
  have h1 := pointsToBytes_entails_memRegion (sp + 0x328#64) tail
  rw [htail] at h1
  exact sepConj_mono h1
    (sepConj_mono (Entails.sepExists_right q0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right q1 (Entails.refl _))
        (sepConj_mono_left (Entails.sepExists_right w8 (Entails.refl _)))))

theorem join_324_to_adc (sp : BitVec 64) :
    memRegion (sp + 0x324#64) 4 ∗
      memRegion (sp + 0x328#64) 0x188 ∗
      memRegion (sp + 0x4b0#64) 0x140 ∗
      memRegion (sp + 0x5f0#64) 368 ∗
      memRegion (sp + 0x760#64) 0x6a0 =
      memRegion (sp + 0x324#64) 0xadc := by
  rw [memRegion_split (sp + 0x324#64) 4 0xad8 (by decide),
      memRegion_split (sp + 0x324#64 + 4#64) 0x188 0x950 (by decide),
      memRegion_split (sp + 0x324#64 + 4#64 + 0x188#64) 0x140 0x810 (by decide),
      memRegion_split (sp + 0x324#64 + 4#64 + 0x188#64 + 0x140#64) 368 0x6a0 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem split_5f0_for_noRecord (sp w0 w1 : BitVec 64) (w2 : BitVec 32)
    (q0 q1 : BitVec 128) (w8 : BitVec 32) (tail : List (BitVec 8)) (htail : tail.length = 312) :
    ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
      ((sp + 0x600#64) ↦₃₂ w2) ∗ ((sp + 0x604#64) ↦₁₂₈ q0) ∗
      ((sp + 0x614#64) ↦₁₂₈ q1) ∗ ((sp + 0x624#64) ↦₃₂ w8) ∗
      ((sp + 0x628#64) ↦ₛ tail) ⊢
      memRegion (sp + 0x5f0#64) 24 ∗
      (∃∗ b0 : BitVec 8, ((sp + 0x608#64) ↦₈ b0)) ∗
      (∃∗ pad : List (BitVec 8), ⌜pad.length = 7⌝ ∗ ((sp + 0x609#64) ↦ₛ pad)) ∗
      (∃∗ d0 : BitVec 64, ((sp + 0x610#64) ↦₆₄ d0)) ∗
      (∃∗ d1 : BitVec 64, ((sp + 0x618#64) ↦₆₄ d1)) ∗
      memRegion (sp + 0x620#64) 320 := by
  have h56 :
      ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2) ∗ ((sp + 0x604#64) ↦₁₂₈ q0) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1) ∗ ((sp + 0x624#64) ↦₃₂ w8) ⊢
        memRegion (sp + 0x5f0#64) 56 := by
    rw [memRegion_split (sp + 0x5f0#64) 8 48 (by decide),
        memRegion_split (sp + 0x5f0#64 + 8#64) 8 40 (by decide),
        memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64) 4 36 (by decide),
        memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 4#64) 16 20 (by decide),
        memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 4#64 + 16#64) 16 4 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd,
      ProofLib.memRegion_eight, ProofLib.memRegion_four, memRegion_16_eq_exists_pointsTo128]
    exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
          (sepConj_mono (Entails.sepExists_right q0 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right q1 (Entails.refl _))
              (Entails.sepExists_right w8 (Entails.refl _))))))
  have h312 := pointsToBytes_entails_memRegion (sp + 0x628#64) tail
  rw [htail] at h312
  have h368 : memRegion (sp + 0x5f0#64) 56 ∗ memRegion (sp + 0x628#64) 312 =
      memRegion (sp + 0x5f0#64) 368 := by
    rw [memRegion_split (sp + 0x5f0#64) 56 312 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hreord :
      (((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2) ∗ ((sp + 0x604#64) ↦₁₂₈ q0) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1) ∗ ((sp + 0x624#64) ↦₃₂ w8) ∗
        ((sp + 0x628#64) ↦ₛ tail)) =
      ((((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2) ∗ ((sp + 0x604#64) ↦₁₂₈ q0) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1) ∗ ((sp + 0x624#64) ↦₃₂ w8)) ∗
        ((sp + 0x628#64) ↦ₛ tail)) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono h56 h312) ?_
  rw [h368,
      memRegion_split (sp + 0x5f0#64) 24 344 (by decide),
      memRegion_split (sp + 0x5f0#64 + 24#64) 1 343 (by decide),
      memRegion_split (sp + 0x5f0#64 + 24#64 + 1#64) 7 336 (by decide),
      memRegion_split (sp + 0x5f0#64 + 24#64 + 1#64 + 7#64) 8 328 (by decide),
      memRegion_split (sp + 0x5f0#64 + 24#64 + 1#64 + 7#64 + 8#64) 8 320 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_one, ProofLib.memRegion_eight,
    memRegion_eq_exists_bytes (sp + 0x609#64) 7 (by decide)]
  exact Entails.refl _

theorem fold_5f0_after_noRecord (sp w0 : BitVec 64) (w1 : BitVec 32)
    (q0 q1 : BitVec 128) (w8 : BitVec 32) :
    ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₃₂ w1) ∗
      ((sp + 0x5fc#64) ↦₁₂₈ q0) ∗ ((sp + 0x60c#64) ↦₁₂₈ q1) ∗
      ((sp + 0x61c#64) ↦₃₂ w8) ∗ memRegion (sp + 0x620#64) 320 ⊢
      memRegion (sp + 0x5f0#64) 368 := by
  rw [memRegion_split (sp + 0x5f0#64) 8 360 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64) 4 356 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 4#64) 16 340 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 4#64 + 16#64) 16 324 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 4#64 + 16#64 + 16#64) 4 320 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight, ProofLib.memRegion_four, memRegion_16_eq_exists_pointsTo128]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right q0 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right q1 (Entails.refl _))
          (sepConj_mono_left (Entails.sepExists_right w8 (Entails.refl _))))))

/-! ## 4. Callee & Model Helpers for `SegDispatch` -/

theorem stringClone_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hSC : HookSat abs stringCloneHookName (stringCloneSpec A)) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) stringCloneHookName (stringCloneSpec A) := by
  have habs := tripleRatchetExterns_stores_abs C ctl abs
  have h6 : Rust.withPanics (tripleRatchetExterns C ctl abs) stringCloneHookName =
      abs stringCloneHookName := Option.some.inj (congrArg (·[6]?) habs)
  simpa [HookSat, h6] using hSC

theorem stringClone_ok_at_dec {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (_hSC : HookSat abs stringCloneHookName (stringCloneSpec A))
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr msgDecryptName + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "session_message_decrypt_signal")) (stringCloneSpec A) := by
  exact sub_ok_at_of_fnAddr
    (LibsignalBinary.Proofs.Common.StringCloneFlat.stringClone_tripleRatchetProgAt_ok b C A ctl abs hA)
    msgDecryptName (num% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - ls_off% "session_message_decrypt_signal"))
    (by simp only [LibsignalBinary.Proofs.Common.StringCloneFlat.stringCloneName_fnOff, arm64_norm])

theorem msgDecrypt_memcpy_ok {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr msgDecryptName + bv% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal")) framelessMemcpySpec := by
  exact framelessMemcpy_ok_at (b := b) (C := C) (ctl := ctl)
    (abs := abs) (name := msgDecryptName) (k := num% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))

theorem msgDecrypt_dealloc_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr msgDecryptName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "session_message_decrypt_signal")) (rustDeallocSpec A) := by
  exact dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := msgDecryptName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "session_message_decrypt_signal")) hA

theorem api_run_storeCall_err {Addr PQ E α β : Type} (c : StoreCall Addr PQ) (e : E)
    (k : α → Api Addr PQ E β) :
    Api.run (storeCall c (.error e) >>= k) = (.error (.store e), [c]) := rfl

theorem api_run_storeCall_ok {Addr PQ E α β : Type} (c : StoreCall Addr PQ) (a : α)
    (k : α → Api Addr PQ E β) :
    Api.run (storeCall c (.ok a) >>= k) = (ExceptT.run (k a)).run [c] := rfl

theorem model_of_load_err (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (hload : ans.loadSession = .error ()) :
    x.model C S uuidTryParse ans = (.error (.store ()), [.loadSession x.rem.val]) ∧
    x.draws C ans = 0 := by
  refine ⟨?_, ?_⟩
  · unfold DecryptGhost.model messageDecryptSignal
    rw [hload]
    rfl
  · simp [DecryptGhost.draws, loadedSession, hload]

theorem model_of_load_none (C : Crypto) (S : SpqrModel)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (hload : ans.loadSession = .ok none) :
    x.model C S uuidTryParse ans =
      (.error (.sessionNotFound x.rem.val "message_decrypt_signal"),
        [.loadSession x.rem.val]) ∧
    x.draws C ans = 0 := by
  refine ⟨?_, ?_⟩
  · unfold DecryptGhost.model messageDecryptSignal
    rw [hload, api_run_storeCall_ok]
    rfl
  · simp [DecryptGhost.draws, loadedSession, hload]

theorem tapeAt_entails_tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  apply Entails.pure_left; intro _
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem allocFailedIn_trans' {s0 sm sf : State}
    (h0m : s0.trace <+: sm.trace) (hmf : allocFailedIn sm sf) :
    allocFailedIn s0 sf := by
  obtain ⟨t, ht⟩ := h0m
  unfold allocFailedIn at hmf ⊢
  rw [← ht, List.length_append, ← List.drop_drop] at hmf
  exact List.mem_of_mem_drop hmf

theorem stringClone_onPanic_entails {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (h0s : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecSpecV, Spec.inImage]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨h0s.trans hpref, Or.inl (allocFailedIn_trans' h0s halloc)⟩
    (entails_anyHeap _)

theorem drop_ne (b : BitVec 64) (hb : b &&& 0xfff#64 = 0#64) : b + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744) ≠ 0#64 := by
  intro h
  rw [show b = 0#64 - bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 15744) by rw [← h, BitVec.add_sub_cancel]] at hb
  exact absurd hb (by decide)

theorem loadPollOutAt_err_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (b sp : BitVec 64) :
    loadPollOutAtS Scope A b (sp + 0x5f0#64) (.error ()) ⊢
      ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFE#64 0x800000000000001A#64
          (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) 10#64 1#64 (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)) w6 ∗
        ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr) ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  dsimp only [loadPollOutAtS]
  rw [memRegion_split (sp + 0x5f0#64 + 0x30#64) 8 312 (by decide),
      ProofLib.memRegion_eight,
      memRegion_eq_exists_bytes (sp + 0x5f0#64 + 0x30#64 + 8#64) 312 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  apply Entails.sepExists_elim; intro w6
  refine Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)
  unfold recordWords56At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem loadPollOutAt_none_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (b sp : BitVec 64) :
    loadPollOutAtS Scope A b (sp + 0x5f0#64) (.ok none) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFF#64 w1 w2 w3 w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  dsimp only [loadPollOutAtS]
  rw [memRegion_split (sp + 0x5f0#64 + 8#64) 8 352 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64) 8 344 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 8#64) 8 336 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 328 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 320 (by decide),
      memRegion_split (sp + 0x5f0#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 312 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    ProofLib.memRegion_eight,
    memRegion_eq_exists_bytes (sp + 0x628#64) 312 (by decide),
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
      (Entails.sepExists_right w5 (Entails.sepExists_right w6
        (Entails.sepExists_right tail ?_))))))
  unfold recordWords56At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem loadPollOutAt_some_entails (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b sp : BitVec 64) (rec : SessionRecord (List (BitVec 8))) :
    loadPollOutAtS Scope A b (sp + 0x5f0#64) (.ok (some rec)) ⊢
      ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧ g.prevCap.toNat < 2 ^ 63⌝ ∗
        recordWords56At (sp + 0x5f0#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) ∗ recordHeap A g rec := by
  dsimp only [loadPollOutAtS]
  apply Entails.pure_left; intro hscope
  apply Entails.sepExists_elim; intro g
  rw [sessionRecordAt_eq_words56_sep_tail A (sp + 0x5f0#64) g rec]
  apply Entails.sepExists_elim; intro w4
  apply Entails.sepExists_elim; intro w5
  apply Entails.sepExists_elim; intro w6
  apply Entails.sepExists_elim; intro tail
  apply Entails.pure_left; intro htail
  refine Entails.sepExists_right g (Entails.sepExists_right w4
    (Entails.sepExists_right w5 (Entails.sepExists_right w6
      (Entails.sepExists_right tail ?_))))
  have hcap := recordHeap_prevCap_lt_two_pow_63 A g rec
  have hpull :
      (recordWords56At (sp + 0x5f0#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((sp + 0x5f0#64 + 0x38#64) ↦ₛ tail) ∗ recordHeap A g rec) =
      (recordHeap A g rec ∗
        recordWords56At (sp + 0x5f0#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail)) := by
    have h628 : sp + 0x5f0#64 + 0x38#64 = sp + 0x628#64 := by bv_arith
    rw [h628]; ac_rfl
  rw [hpull]
  refine Entails.trans (sepConj_mono_left hcap) ?_
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hlt
  apply Entails.pure_right ⟨hscope, htail, hlt⟩
  exact Entails.of_eq (by ac_rfl)

def loadPollBranchRest (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .error () =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
      w2 = b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")) ∧ w3 = 10#64 ∧ w4 = 1#64 ∧ w5 = b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16)⌝ ∗
      ((b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))) ↦ᵣ storeHookStr)
  | .ok none =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝
  | .ok (some rec) =>
    ∃∗ g : RecordGhost,
      ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧
        g.prevCap.toNat < 2 ^ 63 ∧
        w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g⌝ ∗
      recordHeap A g rec

theorem loadPollOutAt_entails_common (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (b sp : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    loadPollOutAtS Scope A b (sp + 0x5f0#64) ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        loadPollBranchRest Scope A b w0 w1 w2 w3 w4 w5 w6 tail ans ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  have hrep : ∀ w0 w1 w2 w3 w4 w5 w6 : BitVec 64,
      recordWords56At (sp + 0x5f0#64) w0 w1 w2 w3 w4 w5 w6 =
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) := by
    intro w0 w1 w2 w3 w4 w5 w6
    rw [recordWords56At_repack]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rcases ans with ⟨⟨⟩⟩ | (_ | rec)
  · refine Entails.trans (loadPollOutAt_err_entails A b sp) ?_
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64
      (Entails.sepExists_right 0x800000000000001A#64
        (Entails.sepExists_right (b + bv% (ls_reloc% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}")))
          (Entails.sepExists_right 10#64
            (Entails.sepExists_right 1#64
              (Entails.sepExists_right (b + bv% (ls_xref% (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 620) (ls_off% "<libsignal_protocol::fingerprint::ScannableFingerprint>::serialize" + 624) + 16))
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    dsimp only [loadPollBranchRest]
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollOutAt_none_entails A b sp) ?_
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64
      (Entails.sepExists_right w1
        (Entails.sepExists_right w2
          (Entails.sepExists_right w3
             (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ ⌜_⌝ ∗ _
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollOutAt_some_entails Scope A b sp rec) ?_
    apply Entails.sepExists_elim; intro g
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; rintro ⟨hscope, htail_inl, hlt⟩
    have hne := (ne_neg_tags_of_lt_two_pow_63 hlt).2.2
    rw [hrep]
    refine Entails.sepExists_right g.prevCap
      (Entails.sepExists_right g.prevPtr
        (Entails.sepExists_right 0#64
          (Entails.sepExists_right (recordCurCap g)
            (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ (∃∗ g', ⌜_⌝ ∗ _) ∗ _
    apply Entails.pure_right ⟨hne, htail_inl.1⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    rw [sepConj_comm ((sp + 0x628#64) ↦ₛ tail) (recordHeap A g rec)]
    refine sepConj_mono_left (Entails.sepExists_right g ?_)
    exact Entails.pure_right ⟨hscope, htail_inl, hlt, by trivial⟩ (Entails.refl _)

theorem fold_words56_repack (p w0 w1 w2 w3 w4 w5 w6 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗
      ((p + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗
      ((p + 0x14#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
      ((p + 0x24#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
      ((p + 0x34#64) ↦₃₂ w6.extractLsb' 32 32) ⊢
      recordWords56At p w0 w1 w2 w3 w4 w5 w6 :=
  Entails.of_eq (recordWords56At_repack p w0 w1 w2 w3 w4 w5 w6).symm

theorem fold_5f0_368 (sp w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8))
    (htail : tail.length = 312) :
    ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
      ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
      ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
      ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
      ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
      ((sp + 0x628#64) ↦ₛ tail) ⊢
      memRegion (sp + 0x5f0#64) 368 := by
  have hrep := recordWords56At_repack (sp + 0x5f0#64) w0 w1 w2 w3 w4 w5 w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep
  have hreord :
      (((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        ((sp + 0x628#64) ↦ₛ tail)) =
      ((((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
        ((sp + 0x628#64) ↦ₛ tail)) := by ac_rfl
  rw [hreord, ← hrep, memRegion_split (sp + 0x5f0#64) 56 312 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h1 := pointsToBytes_entails_memRegion (sp + 0x628#64) tail
  rw [htail] at h1
  exact sepConj_mono (recordWords56At_entails_memRegion _ _ _ _ _ _ _ _) h1

theorem repack_after_0x3a980 (sp ptr w3 w4 w5 w6 : BitVec 64) (dev : BitVec 8)
    (pad : List (BitVec 8)) (hw4 : dev :: pad = unpack64 w4) :
    ((sp + 0x5f8#64) ↦₃₂ ptr.extractLsb' 0 32) ∗
      ((sp + 0x5fc#64) ↦₃₂ ptr.extractLsb' 32 32) ∗
      ((sp + 0x600#64) ↦₆₄ w3) ∗
      ((sp + 0x608#64) ↦₈ dev) ∗ ((sp + 0x609#64) ↦ₛ pad) ∗
      ((sp + 0x610#64) ↦₆₄ w5) ∗ ((sp + 0x618#64) ↦₆₄ w6) ⊢
    ((sp + 0x5f8#64) ↦₃₂ ptr.extractLsb' 0 32) ∗
      ((sp + 0x5fc#64) ↦₁₂₈ q0OfWords ptr w3 w4) ∗
      ((sp + 0x60c#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
      ((sp + 0x61c#64) ↦₃₂ w6.extractLsb' 32 32) := by
  have hptr : ((sp + 0x5f8#64) ↦₃₂ ptr.extractLsb' 0 32) ∗
      ((sp + 0x5fc#64) ↦₃₂ ptr.extractLsb' 32 32) = ((sp + 0x5f8#64) ↦₆₄ ptr) := by
    have h := (pointsTo64_split32 (sp + 0x5f8#64) ptr).symm
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hdev : ((sp + 0x608#64) ↦₈ dev) ∗ ((sp + 0x609#64) ↦ₛ pad) =
      ((sp + 0x608#64) ↦₆₄ w4) := by
    have h := pointsTo64_of_cons_unpack64 (sp + 0x608#64) dev pad w4 hw4
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have hrep := words5_repack_w32_2q128_w32 (sp + 0x5e8#64) ptr w3 w4 w5 w6
  unfold q0OfWords q1OfWords q0Lo q0Hi q1Lo q1Hi
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrep
  rw [← sepConj_assoc ((sp + 0x5f8#64) ↦₃₂ _), hptr,
      ← sepConj_assoc ((sp + 0x608#64) ↦₈ _), hdev, hrep]
  exact Entails.refl _

/-! ## 5. `SepWPp` / `DecSeg` Infrastructure -/

structure FrozenInv (img : Obj.Image) (s : State) : Prop where
  frozen : img.FrozenLoaded s
  symtab : s.symtab = img.symtab

theorem FrozenInv.of_steps {prog : Program} {img : Obj.Image} {s sf : State}
    (h : FrozenInv img s) (hsteps : Steps prog s sf) : FrozenInv img sf :=
  ⟨h.1.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans h.2⟩

theorem messageDecrypt_of_sepWP_frozen {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog mid s P
      (fun sm Pm => FrozenInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hF.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem messageDecrypt_of_sepWP_done {prog : Program} {img : Obj.Image} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (h : SepWP prog ret s P (fun sf P_f => FrozenInv img sf → Q sf P_f)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq (hF.of_steps hsteps)⟩⟩

theorem messageDecrypt_call_panic_then_wp_frozen {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hF : FrozenInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => FrozenInv img sf' → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  refine SepWPp.call_wpp_frozen hcall hF.frozen hF.symtab hpc hrun hsp_align hlr hpre
    (fun sf code R' _ hpost => ?_)
    (fun sf _ _ hm' => Satisfies.mono (sepConj_mono_left (hpan sf)) hm')
    (fun sm hpcm hrunm hspm hcsm hfz_m hsym_m =>
      messageDecrypt_of_sepWP_done ⟨hfz_m, hsym_m⟩ (hnext sm hpcm hrunm hspm hcsm))
    (fun sf R' hoom_st hoom_post => False.elim (hoom sf (F ∗ R') hoom_st hoom_post))
  rw [hexit_eq] at hpost
  exact not_satisfies_false_sepConj hpost

theorem decSeg_of_sepWP_mid {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) mid s P
      (fun sm Pm => FrozenInv img sm → (sm.mem ⊨ Pm ∗ R) →
        DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 sm Out)) :
    DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hF.of_steps hsteps) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSeg_of_sepWP_done {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hF : FrozenInv img s) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => FrozenInv img sf → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hF.of_steps hsteps) hmf)⟩

theorem decSeg_of_sepWPp {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

/-! ## Relocatable `[LibsignalPlacement]` Helpers -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

theorem apiDecResultAt_store_placed_of_words (A : RustAlloc) (strPtr vt w6 r : BitVec 64) :
    ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ strPtr) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
      ((r + 0x20#64) ↦₆₄ vt) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
      (strPtr ↦ᵣ storeHookStr)) ⊢
      apiDecResultAt A r (.error (.store ())) := by
  dsimp only [apiDecResultAt, apiErrAt]
  have hspe : speWord speApplicationCallback = 0x800000000000001A#64 := rfl
  have hstr : (((r + 8#64) ↦₆₄ strPtr) ∗
      ((r + 0x10#64) ↦₆₄ 10#64) ∗ (strPtr ↦ᵣ storeHookStr)) ⊢
      strRefAt (r + 8#64) storeHookStr := by
    have hlen : BitVec.ofNat 64 storeHookStr.length = 10#64 := by rfl_kernel
    have h10 : r + 8#64 + 8#64 = r + 0x10#64 := by bv_arith
    have h := strRefAt_intro (r + 8#64) strPtr storeHookStr
    rwa [hlen, h10] at h
  have hd : ((r + 0x18#64) ↦₆₄ 1#64) ⊢ ∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((r + 0x18#64) ↦₆₄ d) :=
    Entails.sepExists_right 1#64 (Entails.pure_right (by decide) (Entails.refl _))
  have hvt : ((r + 0x20#64) ↦₆₄ vt) ⊢ ∃∗ vt' : BitVec 64, ((r + 0x20#64) ↦₆₄ vt') :=
    Entails.sepExists_right vt (Entails.refl _)
  have hm8 : ((r + 0x28#64) ↦₆₄ w6) ⊢ memRegion (r + 0x28#64) 8 := by
    rw [ProofLib.memRegion_eight]
    exact Entails.sepExists_right w6 (Entails.refl _)
  rw [hspe]
  have hreord :
      ((r ↦₆₄ 0x800000000000001A#64) ∗ ((r + 8#64) ↦₆₄ strPtr) ∗
        ((r + 0x10#64) ↦₆₄ 10#64) ∗ ((r + 0x18#64) ↦₆₄ 1#64) ∗
        ((r + 0x20#64) ↦₆₄ vt) ∗ ((r + 0x28#64) ↦₆₄ w6) ∗
        (strPtr ↦ᵣ storeHookStr)) =
      ((r ↦₆₄ 0x800000000000001A#64) ∗
        (((r + 8#64) ↦₆₄ strPtr) ∗ ((r + 0x10#64) ↦₆₄ 10#64) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
        ((r + 0x18#64) ↦₆₄ 1#64) ∗ ((r + 0x20#64) ↦₆₄ vt) ∗
        ((r + 0x28#64) ↦₆₄ w6)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono_right (sepConj_mono hstr (sepConj_mono hd (sepConj_mono hvt hm8)))

theorem stagedRes_store_err_placed (A : RustAlloc) (src strPtr vt w6 : BitVec 64) :
    (((src ↦₁₂₈ q0OfWords strPtr 10#64 1#64) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords 1#64 vt w6) ∗
      ((src + 0x20#64) ↦₃₂ w6.extractLsb' 32 32)) ∗
      (strPtr ↦ᵣ storeHookStr)) ⊢
      StagedRes A 0x800000000000001A#64
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (strPtr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (strPtr.extractLsb' 0 32))
        src (.error (.store ())) :=
  stagedRes_of_words5 A src 0x800000000000001A#64 strPtr 10#64 1#64
    vt w6 (strPtr ↦ᵣ storeHookStr) (.error (.store ()))
    (apiDecResultAt_store_placed_of_words A strPtr vt w6)

theorem apiDecResultAt_sessionNotFound_placed_of_words (A : RustAlloc) (a : AddrVal)
    (cap ptr strPtr w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) (r : BitVec 64) :
    ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
      ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
      ((r + 0x18#64) ↦₆₄ w4) ∗
      ((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
      (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      apiDecResultAt A r (.error (.sessionNotFound a "message_decrypt_signal")) := by
  dsimp only [apiDecResultAt, apiErrAt, addrCloneAt]
  have hvec := vecU8_intro A r cap ptr a.name
  have hw4_ent := pointsTo64_entails_byte_memRegion7 (r + 0x18#64) a.device pad w4 hpad hw4
  have h19 : r + 0x18#64 + 1#64 = r + 0x19#64 := by bv_arith
  rw [h19] at hw4_ent
  have hstr : (((r + 0x20#64) ↦₆₄ strPtr) ∗
      ((r + 0x28#64) ↦₆₄ 22#64) ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal")) ⊢
      strRefAt (r + 0x20#64) (utf8 "message_decrypt_signal") := by
    have hlen : BitVec.ofNat 64 (utf8 "message_decrypt_signal").length = 22#64 := by rfl_kernel
    have h28 : r + 0x20#64 + 8#64 = r + 0x28#64 := by bv_arith
    have h := strRefAt_intro (r + 0x20#64) strPtr (utf8 "message_decrypt_signal")
    rwa [hlen, h28] at h
  have hreord :
      ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
        ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
        ((r + 0x18#64) ↦₆₄ w4) ∗
        ((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
        (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) =
      ((((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗
          ((r + 0x10#64) ↦₆₄ BitVec.ofNat 64 a.name.length) ∗
          vecU8Buf A cap ptr a.name) ∗
        ((r + 0x18#64) ↦₆₄ w4)) ∗
        (((r + 0x20#64) ↦₆₄ strPtr) ∗ ((r + 0x28#64) ↦₆₄ 22#64) ∗
          (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) := by ac_rfl
  rw [hreord]
  exact sepConj_mono (sepConj_mono hvec hw4_ent) hstr

theorem stagedRes_sessionNotFound_placed (A : RustAlloc) (src : BitVec 64) (a : AddrVal)
    (cap ptr strPtr w4 : BitVec 64) (pad : List (BitVec 8))
    (hpad : pad.length = 7) (hw4 : a.device :: pad = unpack64 w4) :
    (((src ↦₁₂₈ q0OfWords ptr (BitVec.ofNat 64 a.name.length) w4) ∗
      ((src + 0x10#64) ↦₁₂₈ q1OfWords w4 strPtr 22#64) ∗
      ((src + 0x20#64) ↦₃₂ 0#32)) ∗
      (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))) ⊢
      StagedRes A cap
        (BitVec.zeroExtend 64
          (BitVec.truncate 32 (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32) >>> 8)))
        (BitVec.zeroExtend 64 (ptr.extractLsb' 0 32))
        src (.error (.sessionNotFound a "message_decrypt_signal")) := by
  have h22 : (22#64 : BitVec 64).extractLsb' 32 32 = 0#32 := rfl
  rw [← h22]
  exact stagedRes_of_words5 A src cap ptr (BitVec.ofNat 64 a.name.length) w4
    strPtr 22#64
    (vecU8Buf A cap ptr a.name ∗ (strPtr ↦ᵣ utf8 "message_decrypt_signal"))
    (.error (.sessionNotFound a "message_decrypt_signal"))
    (apiDecResultAt_sessionNotFound_placed_of_words A a cap ptr strPtr w4 pad hpad hw4)

theorem messageDecrypt_of_sepWP_lscro [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem messageDecrypt_of_sepWP_done_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog ret s P (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → Q sf P_f)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hq (hcrl.of_keepsFrozen hsteps.keepsFrozen)⟩⟩

theorem messageDecrypt_call_panic_then_wp_lscro [LibsignalPlacement] {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F R : SepProp} {Qpan : State → SepProp}
    {post : State → SepProp → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R' : SepProp, (s.mem ⊨ P ∗ R') → (s.mem ⊨ spec.pre x s ∗ (F ∗ R')))
    (hpan : ∀ sf, spec.onPanic x s sf ∗ F ⊢ Qpan sf)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf (spec.post x s sf ∗ F)
        (fun sf' P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf'.mem → post sf' P_f))
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Qpan sf ∗ R)) := by
  intro R' hm hL
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun (hpre R' hm) hsp_align hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpc', hrun', P_f, hmf, hq⟩ | ⟨_, _hoom⟩⟩ :=
      (hnext sm hpcm hrunm hspm hcsm).elim hpost (hsteps.codeLoaded hL)
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    exact ⟨sf, hsteps.trans hsteps', Or.inl ⟨hpc', hrun', P_f, hmf, hq (hcrl_m.of_keepsFrozen hsteps'.keepsFrozen)⟩⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost,
      fun hm' => Satisfies.mono (sepConj_mono_left (hpan sm)) hm'⟩)⟩
  · rw [hexit_eq] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · exact (hoom sm (F ∗ R') _hoom_st _hoom_post).elim

theorem decSeg_of_sepWP_mid_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_197 H) mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → (sm.mem ⊨ Pm ∗ R) →
        DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 sm Out)) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSeg_of_sepWP_done_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_197 H) target s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩

theorem decSeg_of_sepWPp_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : String → Option (State → State)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_197 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf ∗ R))) :
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

abbrev msgDecryptStrSym : String :=
  "libsignal_session:.rodata..Lanon.125"

theorem satisfies_rodata_msgDecryptStr_placed [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : CryptoVerification.LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ msgDecryptStrSym) ↦ᵣ utf8 "message_decrypt_signal") ∗ P :=
  CryptoVerification.lsro_slice_intro hro (off := 0) (BitVec.add_zero _).symm (by rfl_kernel) hP

theorem ls_hook_ok_197 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide) (h : HookSat H sym spec) :
    subroutine_ok (lsProg_197 H) (lsmpl.ρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact CryptoVerification.ls_hook_ok (prog := lsProg_197 H) (i := 197) (k := k)
    (by rw [List.getElem?_eq_getElem hlt, hk]) h

theorem stringClone_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hH : PublicApiDecHooksPlaced A H) :
    subroutine_ok (lsProg_197 H) (lsmpl.base 623)
      (withLsCodeLoaded lsmpl (stringCloneSpec A)) :=
  LibsignalBinary.Proofs.Common.StringClonePlaced.stringClone_placed_codeLoaded_ok
    hH.shim hH.alloc hH.memcpy hH.handleError

theorem msgDecrypt_memcpy_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (hM : HookSat H "memcpy" sessionMemcpyRegionSpec) :
    subroutine_ok (lsProg_197 H) (lsmpl.ρ "memcpy") framelessMemcpySpec :=
  ls_hook_ok_197 (by decide) hM

theorem msgDecrypt_dealloc_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hD : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok (lsProg_197 H) (lsmpl.ρ lsRustDeallocSym) (rustDeallocSpec A) :=
  ls_hook_ok_197 (by decide) hD

theorem stringClone_onPanic_entails_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (h0s : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecV]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨h0s.trans hpref, Or.inl (allocFailedIn_trans' h0s halloc)⟩
    (entails_anyHeap _)

theorem loadPollPlacedOutAt_err_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (sp : BitVec 64) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.error ()) ⊢
      ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFE#64 0x800000000000001A#64
          strPtr 10#64 1#64 vt w6 ∗
        (strPtr ↦ᵣ storeHookStr) ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  dsimp only [StoreKit.loadPollPlacedOutAtS]
  apply Entails.sepExists_elim; intro strPtr
  apply Entails.sepExists_elim; intro vt
  rw [memRegion_split (sp + 0x5f0#64 + 0x30#64) 8 312 (by decide),
      ProofLib.memRegion_eight,
      memRegion_eq_exists_bytes (sp + 0x5f0#64 + 0x30#64 + 8#64) 312 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro tail
  apply Entails.sepExists_elim; intro w6
  refine Entails.sepExists_right strPtr (Entails.sepExists_right vt
    (Entails.sepExists_right w6 (Entails.sepExists_right tail ?_)))
  unfold recordWords56At
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem loadPollPlacedOutAt_none_entails {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (A : RustAlloc) (sp : BitVec 64) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.ok none) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜tail.length = 312⌝ ∗
        recordWords56At (sp + 0x5f0#64) 0xFFFFFFFFFFFFFFFF#64 w1 w2 w3 w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) :=
  loadPollOutAt_none_entails (Scope := Scope) A 0#64 sp

theorem loadPollPlacedOutAt_some_entails (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (sp : BitVec 64) (rec : SessionRecord (List (BitVec 8))) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) (.ok (some rec)) ⊢
      ∃∗ g : RecordGhost, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧ g.prevCap.toNat < 2 ^ 63⌝ ∗
        recordWords56At (sp + 0x5f0#64) g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6 ∗
        ((sp + 0x628#64) ↦ₛ tail) ∗ recordHeap A g rec :=
  loadPollOutAt_some_entails Scope A 0#64 sp rec

def loadPollBranchRestPlaced (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc)
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .error () =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFE#64 ∧ w1 = 0x800000000000001A#64 ∧
      w3 = 10#64 ∧ w4 = 1#64⌝ ∗
      (w2 ↦ᵣ storeHookStr)
  | .ok none =>
    ⌜w0 = 0xFFFFFFFFFFFFFFFF#64⌝
  | .ok (some rec) =>
    ∃∗ g : RecordGhost,
      ⌜Scope rec ∧ RecordTailInline g rec w4 w5 w6 tail ∧
        g.prevCap.toNat < 2 ^ 63 ∧
        w0 = g.prevCap ∧ w1 = g.prevPtr ∧ w2 = 0#64 ∧ w3 = recordCurCap g⌝ ∗
      recordHeap A g rec

theorem loadPollPlacedOutAt_entails_common (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustAlloc) (sp : BitVec 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8))))) :
    StoreKit.loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) ans ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
      ∃∗ tail : List (BitVec 8),
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFD#64 ∧ tail.length = 312⌝ ∗
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) ∗
        loadPollBranchRestPlaced Scope A w0 w1 w2 w3 w4 w5 w6 tail ans ∗
        ((sp + 0x628#64) ↦ₛ tail) := by
  have hrep : ∀ w0 w1 w2 w3 w4 w5 w6 : BitVec 64,
      recordWords56At (sp + 0x5f0#64) w0 w1 w2 w3 w4 w5 w6 =
        ((sp + 0x5f0#64) ↦₆₄ w0) ∗ ((sp + 0x5f8#64) ↦₆₄ w1) ∗
        ((sp + 0x600#64) ↦₃₂ w2.extractLsb' 0 32) ∗
        ((sp + 0x604#64) ↦₁₂₈ q0OfWords w2 w3 w4) ∗
        ((sp + 0x614#64) ↦₁₂₈ q1OfWords w4 w5 w6) ∗
        ((sp + 0x624#64) ↦₃₂ w6.extractLsb' 32 32) := by
    intro w0 w1 w2 w3 w4 w5 w6
    rw [recordWords56At_repack]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rcases ans with ⟨⟨⟩⟩ | (_ | rec)
  · refine Entails.trans (loadPollPlacedOutAt_err_entails A sp) ?_
    apply Entails.sepExists_elim; intro strPtr
    apply Entails.sepExists_elim; intro vt
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFE#64
      (Entails.sepExists_right 0x800000000000001A#64
        (Entails.sepExists_right strPtr
          (Entails.sepExists_right 10#64
            (Entails.sepExists_right 1#64
              (Entails.sepExists_right vt
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    dsimp only [loadPollBranchRestPlaced]
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollPlacedOutAt_none_entails A sp) ?_
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; intro htail
    rw [hrep]
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64
      (Entails.sepExists_right w1
        (Entails.sepExists_right w2
          (Entails.sepExists_right w3
             (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ ⌜_⌝ ∗ _
    apply Entails.pure_right ⟨by decide, htail⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    exact Entails.pure_right (by trivial) (Entails.refl _)
  · refine Entails.trans (loadPollPlacedOutAt_some_entails Scope A sp rec) ?_
    apply Entails.sepExists_elim; intro g
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro w5
    apply Entails.sepExists_elim; intro w6
    apply Entails.sepExists_elim; intro tail
    apply Entails.pure_left; rintro ⟨hscope, htail_inl, hlt⟩
    have hne := (ne_neg_tags_of_lt_two_pow_63 hlt).2.2
    rw [hrep]
    refine Entails.sepExists_right g.prevCap
      (Entails.sepExists_right g.prevPtr
        (Entails.sepExists_right 0#64
          (Entails.sepExists_right (recordCurCap g)
            (Entails.sepExists_right w4
              (Entails.sepExists_right w5
                (Entails.sepExists_right w6
                  (Entails.sepExists_right tail ?_)))))))
    change _ ⊢ ⌜_⌝ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ (∃∗ g', ⌜_⌝ ∗ _) ∗ _
    apply Entails.pure_right ⟨hne, htail_inl.1⟩
    simp only [sepConj_assoc]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_)))))
    rw [sepConj_comm ((sp + 0x628#64) ↦ₛ tail) (recordHeap A g rec)]
    refine sepConj_mono_left (Entails.sepExists_right g ?_)
    exact Entails.pure_right ⟨hscope, htail_inl, hlt, by trivial⟩ (Entails.refl _)

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
