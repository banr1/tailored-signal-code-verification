/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.KyberMarkFit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec

/-!
# CLI Pre-Key, Signed Pre-Key, and Kyber `get` Store Specifications

Instantiates `PreKeyStoreSpec` (`OneTimePreKeyFiles`), `SignedPreKeyStoreSpec`
(`SignedPreKeyFiles`), and `CliKpkGetSide` (`KyberPreKeyFiles`), including the 48-byte
`SignalProtocolError` layouts (`CliGetErr`, `CliReadErr`), future-box `memRegion` entailments,
and 56/48/88-byte sret postcondition bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession.Cli
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## Offsets -/

/-- The `get_pre_key` shim. -/
abbrev cliPkGetShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key")

/-- The `get_pre_key` future's poll. -/
abbrev cliPkGetPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key::{closure#0}")

/-- The `remove_pre_key` shim. -/
abbrev cliPkRemoveShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key")

/-- The `remove_pre_key` future's poll. -/
abbrev cliPkRemovePollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}")

/-- The `get_signed_pre_key` shim. -/
abbrev cliSpkGetShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key")

/-- The `get_signed_pre_key` future's poll. -/
abbrev cliSpkGetPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key::{closure#0}")

/-! ## Separation-logic word and region helpers -/

section CellHelpers

private theorem sepConj_pure_of_true (P : SepProp) {φ : Prop} (hφ : φ) : P ∗ ⌜φ⌝ = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, sepConj_emp]

private theorem pure_sepConj_eq_of_true {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  rw [sepConj_comm, sepConj_pure_of_true P hφ]

private theorem ent_pure_left {φ : Prop} {P Q : SepProp} (h : φ → (P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left h

private theorem ent_pure_right {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) : P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_eq_of_true Q hφ]
  exact h

private theorem ent_bind {α : Type} {X R Q : SepProp} {P : α → SepProp}
    (hX : X ⊢ ∃∗ x, P x) (hk : ∀ x, P x ∗ R ⊢ Q) : X ∗ R ⊢ Q := by
  refine Entails.trans (sepConj_mono_left hX) ?_
  rw [sepExists_sepConj_left]
  exact Entails.sepExists_elim hk

private theorem extractLsb'_zero_append8 {n : Nat} (x : BitVec n) (b : BitVec 8) :
    (x ++ b).extractLsb' 0 8 = b := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hi]

private theorem extractLsb'_shift_append8 {n : Nat} (x : BitVec n) (b : BitVec 8) (k : Nat) :
    (x ++ b).extractLsb' (k + 8) 8 = x.extractLsb' k 8 := by
  ext i hi
  have hlt : ¬(k + 8 + i < 8) := by omega
  have hsub : k + 8 + i - 8 = k + i := by omega
  simp [BitVec.getElem_extractLsb', BitVec.getLsbD_append, hlt, hsub]

private def pack64Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

private theorem pack64Bytes_extract (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 0 8 = b0 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 8 8 = b1 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 16 8 = b2 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 24 8 = b3 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 32 8 = b4 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 40 8 = b5 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 48 8 = b6 ∧
    (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7).extractLsb' 56 8 = b7 := by
  unfold pack64Bytes; refine ⟨extractLsb'_zero_append8 _ b0,
    (extractLsb'_shift_append8 _ b0 0).trans (extractLsb'_zero_append8 _ b1),
    (extractLsb'_shift_append8 _ b0 8).trans ((extractLsb'_shift_append8 _ b1 0).trans (extractLsb'_zero_append8 _ b2)),
    (extractLsb'_shift_append8 _ b0 16).trans ((extractLsb'_shift_append8 _ b1 8).trans
      ((extractLsb'_shift_append8 _ b2 0).trans (extractLsb'_zero_append8 _ b3))),
    (extractLsb'_shift_append8 _ b0 24).trans ((extractLsb'_shift_append8 _ b1 16).trans
      ((extractLsb'_shift_append8 _ b2 8).trans ((extractLsb'_shift_append8 _ b3 0).trans (extractLsb'_zero_append8 _ b4)))),
    (extractLsb'_shift_append8 _ b0 32).trans ((extractLsb'_shift_append8 _ b1 24).trans
      ((extractLsb'_shift_append8 _ b2 16).trans ((extractLsb'_shift_append8 _ b3 8).trans
        ((extractLsb'_shift_append8 _ b4 0).trans (extractLsb'_zero_append8 _ b5))))),
    (extractLsb'_shift_append8 _ b0 40).trans ((extractLsb'_shift_append8 _ b1 32).trans
      ((extractLsb'_shift_append8 _ b2 24).trans ((extractLsb'_shift_append8 _ b3 16).trans
        ((extractLsb'_shift_append8 _ b4 8).trans ((extractLsb'_shift_append8 _ b5 0).trans (extractLsb'_zero_append8 _ b6)))))),
    (extractLsb'_shift_append8 _ b0 48).trans ((extractLsb'_shift_append8 _ b1 40).trans
      ((extractLsb'_shift_append8 _ b2 32).trans ((extractLsb'_shift_append8 _ b3 24).trans
        ((extractLsb'_shift_append8 _ b4 16).trans ((extractLsb'_shift_append8 _ b5 8).trans
          ((extractLsb'_shift_append8 _ b6 0).trans (by ext i hi; simp)))))))⟩

private theorem pointsTo64_eq_bytes8 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦ₛ [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
              w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]) := by
  simp only [pointsTo64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero, BitVec.add_assoc]
  rfl

private theorem pointsTo32_eq_bytes4 (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ w) =
      (a ↦ₛ [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]) := by
  simp only [pointsTo32, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero, BitVec.add_assoc]
  rfl

private theorem pointsTo8_eq_bytes1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

private theorem pointsTo64_entails_memRegion8 (a w : BitVec 64) : (a ↦₆₄ w) ⊢ memRegion a 8 := by
  rw [pointsTo64_eq_bytes8]; exact ProofLib.pointsToBytes_entails_memRegion a _

private theorem pointsTo32_entails_memRegion4 (a : BitVec 64) (w : BitVec 32) :
    (a ↦₃₂ w) ⊢ memRegion a 4 := by
  rw [pointsTo32_eq_bytes4]; exact ProofLib.pointsToBytes_entails_memRegion a _

private theorem pointsTo8_entails_memRegion1 (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  rw [pointsTo8_eq_bytes1]; exact ProofLib.pointsToBytes_entails_memRegion a _

private theorem memRegion8_words (a : BitVec 64) : memRegion a 8 ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) := by
  rw [ProofLib.memRegion_eq_exists_bytes a 8 (by decide)]
  refine Entails.sepExists_elim fun bs => ent_pure_left fun hlen => ?_
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen)
  refine Entails.sepExists_right (pack64Bytes b0 b1 b2 b3 b4 b5 b6 b7) ?_
  have hex := pack64Bytes_extract b0 b1 b2 b3 b4 b5 b6 b7
  rw [pointsTo64_eq_bytes8, hex.1, hex.2.1, hex.2.2.1, hex.2.2.2.1, hex.2.2.2.2.1,
      hex.2.2.2.2.2.1, hex.2.2.2.2.2.2.1, hex.2.2.2.2.2.2.2]
  exact Entails.refl _

private theorem memRegion16_words (a : BitVec 64) :
    memRegion a 16 ⊢ ∃∗ t : BitVec 64 × BitVec 64, (a ↦₆₄ t.1) ∗ ((a + 8#64) ↦₆₄ t.2) := by
  rw [memRegion_split a 8 8 (by decide)]
  refine ent_bind (memRegion8_words a) fun w0 => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion8_words (a + 8#64)) fun w1 => ?_; rw [sepConj_comm]
  exact Entails.sepExists_right (w0, w1) (Entails.refl _)

private theorem memRegion32_words (v : BitVec 64) :
    memRegion v 32 ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64,
        (v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗
          ((v + 16#64) ↦₆₄ t.2.2.1) ∗ ((v + 24#64) ↦₆₄ t.2.2.2) := by
  have h24 : (v + 16#64) + 8#64 = v + 24#64 := by rw [BitVec.add_assoc]; rfl
  rw [memRegion_split v 16 16 (by decide)]
  refine ent_bind (memRegion16_words v) fun ⟨w0, w1⟩ => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion16_words (v + 16#64)) fun ⟨w2, w3⟩ => ?_
  rw [h24, sepConj_comm, sepConj_assoc]
  exact Entails.sepExists_right (w0, w1, w2, w3) (Entails.refl _)

private theorem memRegion40_words (v : BitVec 64) :
    memRegion v 40 ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64,
        (v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗ ((v + 16#64) ↦₆₄ t.2.2.1) ∗
          ((v + 24#64) ↦₆₄ t.2.2.2.1) ∗ ((v + 32#64) ↦₆₄ t.2.2.2.2) := by
  have h16 : (v + 8#64) + 8#64 = v + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : (v + 8#64) + 16#64 = v + 24#64 := by rw [BitVec.add_assoc]; rfl
  have h32 : (v + 8#64) + 24#64 = v + 32#64 := by rw [BitVec.add_assoc]; rfl
  rw [memRegion_split v 8 32 (by decide)]
  refine ent_bind (memRegion8_words v) fun w1 => ?_; rw [sepConj_comm]
  refine ent_bind (memRegion32_words (v + 8#64)) fun ⟨w2, w3, w4, w5⟩ => ?_
  rw [h16, h24, h32, sepConj_comm]
  exact Entails.sepExists_right (w1, w2, w3, w4, w5) (Entails.refl _)

private theorem memRegion_zero_entails_emp (a : BitVec 64) : memRegion a 0 ⊢ emp := by
  rw [ProofLib.memRegion_eq_exists_bytes a 0 (by decide)]
  refine Entails.sepExists_elim fun bs => ent_pure_left fun hlen => ?_
  rcases bs with _ | _
  · rw [pointsToBytes_nil]
    exact Entails.refl _
  · simp at hlen

end CellHelpers

/-! ## Box-to-`memRegion` entailments -/

/-- Any `pkBoxAt` state (`0#8` or `1#8`) entails raw 16-byte `memRegion` ownership for drop. -/
theorem pkBoxAt_memRegion (box self : BitVec 64) (id : BitVec 32) (st : BitVec 8) :
    pkBoxAt box self id st ⊢ memRegion box 16 := by
  unfold pkBoxAt
  rw [show (16 : Nat) = 8 + (4 + (1 + 3)) from rfl,
    memRegion_split box 8 8 (by decide),
    memRegion_split (box + 8#64) 4 4 (by decide),
    memRegion_split (box + 8#64 + 4#64) 1 3 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion8 _ _)
    (sepConj_mono (pointsTo32_entails_memRegion4 _ _)
      (sepConj_mono_left (pointsTo8_entails_memRegion1 _ _)))

/-- Any `kpkMarkBoxAt` state (`0#8` or `1#8`) entails raw 32-byte `memRegion` ownership for drop. -/
theorem kpkMarkBoxAt_memRegion (box self baseKeyA : BitVec 64) (id signedId : BitVec 32)
    (st : BitVec 8) :
    kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32 := by
  unfold kpkMarkBoxAt
  rw [show (32 : Nat) = 8 + (8 + (4 + (4 + (1 + 7)))) from rfl,
    memRegion_split box 8 24 (by decide),
    memRegion_split (box + 8#64) 8 16 (by decide),
    memRegion_split (box + 8#64 + 8#64) 4 12 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 4#64) 4 8 (by decide),
    memRegion_split (box + 8#64 + 8#64 + 4#64 + 4#64) 1 7 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion8 _ _)
    (sepConj_mono (pointsTo64_entails_memRegion8 _ _)
      (sepConj_mono (pointsTo32_entails_memRegion4 _ _)
        (sepConj_mono (pointsTo32_entails_memRegion4 _ _)
          (sepConj_mono_left (pointsTo8_entails_memRegion1 _ _)))))

/-! ## Error types and `SpeErrSpec` layouts -/

/-- Discriminant of a `get_*_pre_key` error arm (`InvalidProtobufEncoding` for `decodeErr`). -/
inductive CliGetErrTag where
  | missing
  | readErr
  | decodeErr
  deriving DecidableEq, Repr

/-- Kit witness for a `get_*_pre_key` `Err` return: error arm plus inline payload words `w1..w5`. -/
structure CliGetErr where
  tag : CliGetErrTag
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

/-- Heap and `.rodata` ownership for `InvalidState("read", String)`. -/
def cliReadErrHeap (A : RustAlloc) (cap ptr len w4 w5 : BitVec 64) : SepProp :=
  (∃∗ bs : List (BitVec 8),
    ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗
  (⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read"))

/-- 48-byte `SignalProtocolError` layout for `get_*_pre_key`, with missing-id SPE index `w`
(`13` for `get_pre_key`, `14` for `get_signed_pre_key`, `15` for `get_kyber_pre_key`). -/
def cliGetErrSpec (A : RustAlloc) (w : Nat) (hw : w < 32 := by decide) : SpeErrSpec CliGetErr where
  w0 := fun e => match e.tag with
    | .missing => speWord w
    | .readErr => speWord 1
    | .decodeErr => speWord 2
  w1 := fun e => e.cap
  w2 := fun e => e.ptr
  w3 := fun e => e.len
  w4 := fun e => e.w4
  w5 := fun e => e.w5
  heap := fun e => match e.tag with
    | .readErr => cliReadErrHeap A e.cap e.ptr e.len e.w4 e.w5
    | .missing | .decodeErr => emp
  w0_ne_err := by
    intro e
    cases e.tag with
    | missing =>
      have hw' : w < 32 := hw
      dsimp only [speWord, errTag]
      bv_omega
    | readErr =>
      dsimp only [speWord, errTag]
      bv_omega
    | decodeErr =>
      dsimp only [speWord, errTag]
      bv_omega
  w0_ne_ok := by
    intro e
    cases e.tag with
    | missing =>
      have hw' : w < 32 := hw
      dsimp only [speWord, okTagVec]
      bv_omega
    | readErr =>
      dsimp only [speWord, okTagVec]
      bv_omega
    | decodeErr =>
      dsimp only [speWord, okTagVec]
      bv_omega
  w0_ne_pending := by
    intro e
    cases e.tag with
    | missing =>
      have hw' : w < 32 := hw
      dsimp only [speWord]
      bv_omega
    | readErr =>
      dsimp only [speWord]
      bv_omega
    | decodeErr =>
      dsimp only [speWord]
      bv_omega

/-- Kit witness for `remove_pre_key`'s `Err` return (`InvalidState("read", String)` only). -/
structure CliReadErr where
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

/-- 48-byte `SignalProtocolError` layout for `CliReadErr` (`speWord 1` + `cliReadErrHeap`). -/
def cliReadErrSpec (A : RustAlloc) : SpeErrSpec CliReadErr where
  w0 := fun _ => speWord 1
  w1 := fun e => e.cap
  w2 := fun e => e.ptr
  w3 := fun e => e.len
  w4 := fun e => e.w4
  w5 := fun e => e.w5
  heap := fun e => cliReadErrHeap A e.cap e.ptr e.len e.w4 e.w5
  w0_ne_err := fun _ => by decide
  w0_ne_ok := fun _ => by decide
  w0_ne_pending := fun _ => by decide

/-! ## Pure answer relations -/

def pkAnsErrTag? {α : Type} : PkAns α → Option CliGetErrTag
  | .found _ => none
  | .missing => some .missing
  | .readErr => some .readErr
  | .decodeErr _ => some .decodeErr

/-- Kit answer relation matching `pa : PkAns α` arm-for-arm against `Except CliGetErr α` with
unconstrained inline words on `.error`. -/
def cliGetAnsRel {α : Type} (pa : PkAns α) : Except CliGetErr α → Prop
  | .ok r => pa = .found r
  | .error e => pkAnsErrTag? pa = some e.tag

theorem cliGetAnsRel_error_iff {α : Type} (pa : PkAns α) :
    (∃ e : CliGetErr, cliGetAnsRel pa (.error e)) ↔ pa.toExcept = .error () := by
  cases pa with
  | found r =>
    simp [cliGetAnsRel, pkAnsErrTag?, PkAns.toExcept]
  | missing =>
    exact ⟨fun _ => rfl, fun _ => ⟨⟨.missing, 0, 0, 0, 0, 0⟩, rfl⟩⟩
  | readErr =>
    exact ⟨fun _ => rfl, fun _ => ⟨⟨.readErr, 0, 0, 0, 0, 0⟩, rfl⟩⟩
  | decodeErr _ =>
    exact ⟨fun _ => rfl, fun _ => ⟨⟨.decodeErr, 0, 0, 0, 0, 0⟩, rfl⟩⟩

theorem cliGetAnsRel_ok_iff {α : Type} (pa : PkAns α) (r : α) :
    cliGetAnsRel pa (.ok r) ↔ pa.toExcept = .ok r := by
  cases pa <;> simp [cliGetAnsRel, PkAns.toExcept]

/-! ## Sret error-arm bridges -/

theorem preKeyDeserialize_error_eq {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PreKeyRecord.deserialize bs = .error e) : e = .invalidProtobufEncoding := by
  unfold PreKeyRecord.deserialize at h
  rcases hd : PreKeyRecordStructure.decode bs with _ | s <;> rw [hd] at h <;> cases h; rfl

theorem signedPreKeyDeserialize_error_eq {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : SignedPreKeyRecord.deserialize bs = .error e) : e = .invalidProtobufEncoding := by
  unfold SignedPreKeyRecord.deserialize at h
  rcases hd : SignedPreKeyRecordStructure.decode bs with _ | s <;> rw [hd] at h <;> cases h; rfl

theorem kyberPreKeyDeserialize_error_eq {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : KyberPreKeyRecord.deserialize bs = .error e) : e = .invalidProtobufEncoding := by
  unfold KyberPreKeyRecord.deserialize at h
  rcases hd : SignedPreKeyRecordStructure.decode bs with _ | s <;> rw [hd] at h <;> cases h; rfl

theorem pkAnsOf_decodeErr_of_all {α : Type}
    {dec : List (BitVec 8) → Except SignalProtocolError α}
    (hall : ∀ bs e, dec bs = .error e → e = .invalidProtobufEncoding)
    {gr : Except Unit (List (BitVec 8))} {e : SignalProtocolError}
    (h : pkAnsOf dec gr = .decodeErr e) : e = .invalidProtobufEncoding := by
  rcases gr with _ | _ | ⟨b, bs⟩
  · cases h
  · cases h
  · dsimp only [pkAnsOf] at h
    rcases hd : dec (b :: bs) with err | r
    · rw [hd] at h
      cases h
      exact hall (b :: bs) e hd
    · rw [hd] at h
      cases h

theorem kpkAnsOf_decodeErr_eq {gr1 gr2 : Except Unit (List (BitVec 8))}
    {e : SignalProtocolError}
    (h : kpkAnsOf (pkAnsOf KyberPreKeyRecord.deserialize gr1)
          (pkAnsOf KyberPreKeyRecord.deserialize gr2) = .decodeErr e) :
    e = .invalidProtobufEncoding := by
  rcases h1 : pkAnsOf KyberPreKeyRecord.deserialize gr1 with r | _ | err1 | _
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h
  · rw [h1] at h; cases h
    exact pkAnsOf_decodeErr_of_all (@kyberPreKeyDeserialize_error_eq) h1
  · rw [h1] at h
    exact pkAnsOf_decodeErr_of_all (@kyberPreKeyDeserialize_error_eq) h

private theorem vecU8_words_read (A : RustAlloc) (v : BitVec 64) :
    (∃∗ bs : List (BitVec 8), vecU8 A v bs) ⊢
      ∃∗ t : BitVec 64 × BitVec 64 × BitVec 64,
        ((v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2.1) ∗ ((v + 16#64) ↦₆₄ t.2.2)) ∗
        (∃∗ bs : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs.length = t.2.2 ∧ bs.length ≤ t.1.toNat ∧ t.1.toNat < 2 ^ 63 ∧
            t.2.1 ≠ 0⌝ ∗
          (if t.1 = 0 then emp
           else A.live t.2.1 t.1.toNat 1 ∗ (t.2.1 ↦ₛ bs) ∗
             memRegion (t.2.1 + BitVec.ofNat 64 bs.length) (t.1.toNat - bs.length))) := by
  refine Entails.sepExists_elim fun bs => ?_
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right (cap, ptr, BitVec.ofNat 64 bs.length) ?_
  dsimp only
  refine sepConj_mono (Entails.refl _) (Entails.sepExists_right bs ?_)
  have hEq :
      (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
        (BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length ∧
          bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) :=
    propext ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  nth_rw 1 [hEq]
  exact Entails.refl _

private theorem strRef_words_read (v : BitVec 64) (lit : List (BitVec 8)) :
    strRefAt v lit ⊢
      ∃∗ t : BitVec 64 × BitVec 64,
        ((v ↦₆₄ t.1) ∗ ((v + 8#64) ↦₆₄ t.2)) ∗
        (⌜t.2 = BitVec.ofNat 64 lit.length⌝ ∗ (t.1 ↦ᵣ lit)) := by
  unfold strRefAt
  refine Entails.sepExists_elim fun p => ?_
  refine Entails.sepExists_right (p, BitVec.ofNat 64 lit.length) ?_
  have ha : asm64% boxSliceLenOff = 8#64 := rfl
  rw [ha, pure_sepConj_eq_of_true _ rfl, sepConj_assoc]
  exact Entails.refl _

/-- Convert `speAt A (utf8 "read") p .invalidState` into `speWordsAt` + `cliReadErrHeap`. -/
theorem speAt_read_invalidState_entails (A : RustAlloc) (p : BitVec 64) :
    speAt A (utf8 "read") p .invalidState ⊢
      ∃∗ e : CliReadErr, speErrAt (cliReadErrSpec A) p e := by
  unfold speAt
  have hp8 : asm64% spePayloadOff = 8#64 := rfl
  have hp32 : asm64% speInvalidStateFnOff = 0x20#64 := rfl
  rw [hp8, hp32]
  have r1 :
      (p ↦₆₄ speWord 1) ∗ (∃∗ bs : List (BitVec 8), vecU8 A (p + 8#64) bs) ∗
        strRefAt (p + 0x20#64) (utf8 "read") =
      (∃∗ bs : List (BitVec 8), vecU8 A (p + 8#64) bs) ∗
        (strRefAt (p + 0x20#64) (utf8 "read") ∗ (p ↦₆₄ speWord 1)) := by ac_rfl
  rw [r1]
  refine ent_bind (vecU8_words_read A (p + 8#64)) fun ⟨cap, ptr, len⟩ => ?_
  have r2 :
      ((((p + 8#64) ↦₆₄ cap) ∗ ((p + 8#64 + 8#64) ↦₆₄ ptr) ∗ ((p + 8#64 + 16#64) ↦₆₄ len)) ∗
        (∃∗ bs : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
            ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) ∗
        (strRefAt (p + 0x20#64) (utf8 "read") ∗ (p ↦₆₄ speWord 1)) =
      strRefAt (p + 0x20#64) (utf8 "read") ∗
        ((p ↦₆₄ speWord 1) ∗ ((p + 8#64) ↦₆₄ cap) ∗ ((p + 8#64 + 8#64) ↦₆₄ ptr) ∗
          ((p + 8#64 + 16#64) ↦₆₄ len) ∗
          (∃∗ bs : List (BitVec 8),
            ⌜BitVec.ofNat 64 bs.length = len ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧
              ptr ≠ 0⌝ ∗
            (if cap = 0 then emp
             else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
               memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)))) := by ac_rfl
  rw [r2]
  refine ent_bind (strRef_words_read (p + 0x20#64) (utf8 "read")) fun ⟨w4, w5⟩ => ?_
  refine Entails.sepExists_right ⟨cap, ptr, len, w4, w5⟩ ?_
  unfold speErrAt speWordsAt cliReadErrSpec cliReadErrHeap
  dsimp only
  have ha16 : p + 8#64 + 8#64 = p + 0x10#64 := by rw [BitVec.add_assoc]; rfl
  have ha24 : p + 8#64 + 16#64 = p + 0x18#64 := by rw [BitVec.add_assoc]; rfl
  have ha40 : p + 0x20#64 + 8#64 = p + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  rw [ha16, ha24, ha40]
  exact Entails.of_eq (by ac_rfl)

/-- Per-arm bridge for any error `PkAns α` at sret size `56 ≤ size ≤ 2^64`: converts `pkAnsAt` into
`errTag` + `speErrAt (cliGetErrSpec A w) (out + 8)` + `memRegion (out + 0x38) (size - 56)`. -/
theorem pkAnsAt_error_entails {α : Type} (A : RustAlloc)
    (resAt : RustAlloc → BitVec 64 → Except SignalProtocolError α → SepProp)
    (size w : Nat) (hw : w < 32) (hsize : 56 ≤ size) (hsize_lt : size ≤ 2 ^ 64)
    (hres : ∀ out, resAt A out (.error .invalidProtobufEncoding) =
      errResultAt A [] size out .invalidProtobufEncoding)
    (out : BitVec 64) {pa : PkAns α}
    (hdec : ∀ e, pa = .decodeErr e → e = .invalidProtobufEncoding)
    (tag : CliGetErrTag) (htag : pkAnsErrTag? pa = some tag) :
    pkAnsAt A resAt size w out pa ⊢
      ∃∗ e : CliGetErr,
        ⌜e.tag = tag⌝ ∗
        ((out ↦₆₄ errTag) ∗ speErrAt (cliGetErrSpec A w hw) (out + 8#64) e ∗
          memRegion (out + 0x38#64) (size - 56)) := by
  have ha16 : (out + 8#64) + 8#64 = out + 0x10#64 := by rw [BitVec.add_assoc]; rfl
  have ha24 : (out + 8#64) + 8#64 + 8#64 = (out + 8#64) + 0x10#64 := by rw [BitVec.add_assoc]; rfl
  have ha32 : (out + 8#64) + 8#64 + 16#64 = (out + 8#64) + 0x18#64 := by rw [BitVec.add_assoc]; rfl
  have ha40 : (out + 8#64) + 8#64 + 24#64 = (out + 8#64) + 0x20#64 := by rw [BitVec.add_assoc]; rfl
  have ha48 : (out + 8#64) + 8#64 + 32#64 = (out + 8#64) + 0x28#64 := by rw [BitVec.add_assoc]; rfl
  cases pa with
  | found _ => cases htag
  | missing =>
    cases htag
    unfold pkAnsAt
    have hlen : size - 16 = 40 + (size - 56) := by omega
    have ha56 : (out + 0x10#64) + 40#64 = out + 0x38#64 := by rw [BitVec.add_assoc]; rfl
    rw [hlen, memRegion_split (out + 0x10#64) 40 (size - 56) (by omega), ha56, ← ha16]
    have r1 :
        (out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord w) ∗
          (memRegion ((out + 8#64) + 8#64) 40 ∗ memRegion (out + 0x38#64) (size - 56)) =
        memRegion ((out + 8#64) + 8#64) 40 ∗
          ((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord w) ∗
            memRegion (out + 0x38#64) (size - 56)) := by ac_rfl
    rw [r1]
    refine ent_bind (memRegion40_words ((out + 8#64) + 8#64)) fun ⟨w1, w2, w3, w4, w5⟩ => ?_
    refine Entails.sepExists_right ⟨.missing, w1, w2, w3, w4, w5⟩ ?_
    refine ent_pure_right rfl ?_
    unfold speErrAt speWordsAt cliGetErrSpec
    dsimp only
    rw [ha24, ha32, ha40, ha48, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | decodeErr err =>
    cases htag
    have herr := hdec err rfl
    subst herr
    dsimp only [pkAnsAt]
    rw [hres out]
    unfold errResultAt speAt
    have hr1 : out + asm64% resultErrSpeOff = out + 8#64 := rfl
    have hr2 : out + asm64% (resultErrSpeOff + speSize) = out + 0x38#64 := rfl
    have hr3 : asm% (resultErrSpeOff + speSize) = 56 := rfl
    have hr4 : (out + 8#64) + asm64% spePayloadOff = (out + 8#64) + 8#64 := rfl
    have hr5 : asm% (speSize - spePayloadOff) = 40 := rfl
    rw [hr1, hr2, hr3, hr4, hr5]
    have r1 :
        (out ↦₆₄ errTag) ∗ (((out + 8#64) ↦₆₄ speWord 2) ∗ memRegion ((out + 8#64) + 8#64) 40) ∗
          memRegion (out + 0x38#64) (size - 56) =
        memRegion ((out + 8#64) + 8#64) 40 ∗
          ((out ↦₆₄ errTag) ∗ ((out + 8#64) ↦₆₄ speWord 2) ∗
            memRegion (out + 0x38#64) (size - 56)) := by ac_rfl
    rw [r1]
    refine ent_bind (memRegion40_words ((out + 8#64) + 8#64)) fun ⟨w1, w2, w3, w4, w5⟩ => ?_
    refine Entails.sepExists_right ⟨.decodeErr, w1, w2, w3, w4, w5⟩ ?_
    refine ent_pure_right rfl ?_
    unfold speErrAt speWordsAt cliGetErrSpec
    dsimp only
    rw [ha24, ha32, ha40, ha48, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  | readErr =>
    cases htag
    unfold pkAnsAt errResultAt
    have hr1 : out + asm64% resultErrSpeOff = out + 8#64 := rfl
    have hr2 : out + asm64% (resultErrSpeOff + speSize) = out + 0x38#64 := rfl
    have hr3 : asm% (resultErrSpeOff + speSize) = 56 := rfl
    rw [hr1, hr2, hr3]
    have r1 :
        (out ↦₆₄ errTag) ∗ speAt A (utf8 "read") (out + 8#64) .invalidState ∗
          memRegion (out + 0x38#64) (size - 56) =
        speAt A (utf8 "read") (out + 8#64) .invalidState ∗
          ((out ↦₆₄ errTag) ∗ memRegion (out + 0x38#64) (size - 56)) := by ac_rfl
    rw [r1]
    refine ent_bind (speAt_read_invalidState_entails A (out + 8#64)) fun er => ?_
    refine Entails.sepExists_right ⟨.readErr, er.cap, er.ptr, er.len, er.w4, er.w5⟩ ?_
    refine ent_pure_right rfl ?_
    unfold speErrAt cliGetErrSpec cliReadErrSpec
    dsimp only
    exact Entails.of_eq (by ac_rfl)

/-! ## `OneTimePreKeyFiles` (`cliPreKeyStoreSpec`) -/

/-- Pure store invariant for `OneTimePreKeyFiles` at key `pid` and initial files `F0`. -/
structure CliPkInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (pid : BitVec 32) (d : DirGhost) : Prop where
  nameOk : PkNameOk pathOk d pid
  sizeOk : PkSizeOk rd F0 d pid
  oneLt : d.changed.length < 2 ^ 32 ∧
    (d.changed.length + 1 < 2 ^ 32 ∨ keyName pid ∈ d.changed.map Prod.fst)

def cliPkStoreAt (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32) (self : BitVec 64) (d : DirGhost) :
    SepProp :=
  ⌜CliPkInv rd F0 pathOk pid d⌝ ∗ dirAt A self d

private theorem setOrPush_length_eq_of_mem (n bs : List (BitVec 8)) :
    ∀ {l : List (List (BitVec 8) × List (BitVec 8))},
      n ∈ l.map Prod.fst → (DirGhost.setOrPush n bs l).length = l.length
  | [], hm => by cases hm
  | e :: es, hm => by
    by_cases h : e.1 = n
    · simp [DirGhost.setOrPush, h]
    · simp only [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hm'
      · exact absurd rfl h
      · simp [DirGhost.setOrPush, h, setOrPush_length_eq_of_mem n bs hm']

private theorem mem_fst_setOrPush_self (n bs : List (BitVec 8)) :
    ∀ l : List (List (BitVec 8) × List (BitVec 8)),
      n ∈ (DirGhost.setOrPush n bs l).map Prod.fst
  | [] => by simp [DirGhost.setOrPush]
  | e :: es => by
    by_cases h : e.1 = n
    · simp [DirGhost.setOrPush, h]
    · simp [DirGhost.setOrPush, h, mem_fst_setOrPush_self n bs es]

theorem CliPkInv.removePreKey {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {pid : BitVec 32} {d : DirGhost} (h : CliPkInv rd F0 pathOk pid d) :
    CliPkInv rd F0 pathOk pid
      (_root_.CryptoVerification.SignalSession.Cli.removePreKey rd F0 d pid).2 := by
  unfold _root_.CryptoVerification.SignalSession.Cli.removePreKey
  rcases d.get rd F0 (keyName pid) with _ | _ | ⟨b, bs⟩
  · exact h
  · exact h
  · refine ⟨h.nameOk, ?_, ?_⟩
    · intro outBs hout
      rw [DirGhost.get_put_self] at hout
      cases hout
      decide
    · refine ⟨?_, Or.inr (mem_fst_setOrPush_self (keyName pid) [] d.changed)⟩
      rcases h.oneLt with ⟨hlen, hroom | hmem⟩
      · exact Nat.lt_of_le_of_lt (setOrPush_length_le (keyName pid) [] d.changed) hroom
      · rw [show (d.put (keyName pid) []).changed = DirGhost.setOrPush (keyName pid) [] d.changed
            from rfl, setOrPush_length_eq_of_mem (keyName pid) [] hmem]
        exact hlen

/-- Concrete `PreKeyStoreSpec` for `OneTimePreKeyFiles` at key `pid` and initial files `F0`. -/
def cliPreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (getShimStk getPollStk removeShimStk removePollStk : Nat) : PreKeyStoreSpec A b where
  pk_vt := b + cliPkVtOff
  PkState := DirGhost
  storeAt := cliPkStoreAt A rd F0 pathOk pid
  getIdOk := fun id => id = pid
  removeIdOk := fun id => id = pid
  envOk := fun f => f = F0
  fdsOk := fun fs => FdsGe3Closed fs
  GetErr := CliGetErr
  RemoveErr := CliReadErr
  getErr := cliGetErrSpec A 13
  removeErr := cliReadErrSpec A
  removeUpdate := fun d id _ => (removePreKey rd F0 d id).2
  getRel := fun d id ans =>
    cliGetAnsRel (pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id))) ans
  removeRel := fun d id ans =>
    match ans with
    | .ok () => (removePreKey rd F0 d id).1 = .ok ()
    | .error _ => (removePreKey rd F0 d id).1 = .error ()
  getShimOff := cliPkGetShimOff
  getFutVtOff := cliPkGetFutVtOff
  getPollOff := cliPkGetPollOff
  getFutDropOff := cliIdFutDropOff
  getBoxSize := 16
  removeShimOff := cliPkRemoveShimOff
  removeFutVtOff := cliPkRemoveFutVtOff
  removePollOff := cliPkRemovePollOff
  removeFutDropOff := cliIdFutDropOff
  removeBoxSize := 16
  getShimStack := getShimStk
  getPollStack := getPollStk
  removeShimStack := removeShimStk
  removePollStack := removePollStk
  getBoxAt := pkBoxAt
  removeBoxAt := pkBoxAt
  getBoxAt_memRegion := pkBoxAt_memRegion
  removeBoxAt_memRegion := pkBoxAt_memRegion
  getBoxSize_ne_zero := by decide
  removeBoxSize_ne_zero := by decide
  getBoxSize_lt := by decide
  removeBoxSize_lt := by decide
  getFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  removeFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

theorem cliPk_getRel_error_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) :
    (∃ e, (cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4).getRel d id (.error e)) ↔
      getPreKey rd F0 d id = .error () := by
  rw [getPreKey_eq]
  exact cliGetAnsRel_error_iff _

theorem cliPk_getRel_ok_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) (r : PreKeyRecord) :
    (cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4).getRel d id (.ok r) ↔
      getPreKey rd F0 d id = .ok r := by
  rw [getPreKey_eq]
  exact cliGetAnsRel_ok_iff _ r

theorem cliPreKeyStoreSpec_quiet {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) :
    (cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4).Quiet :=
  ⟨fun _ _ => by simp [cliPreKeyStoreSpec, NoFsEv],
    fun _ _ => by simp [cliPreKeyStoreSpec, NoFsEv]⟩

theorem cliPreKeyStoreSpec_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) :
    PreKeyVtablesOk img (cliPreKeyStoreSpec A img.base rd F0 pathOk pid s1 s2 s3 s4) where
  getSlot := cliPkGetSlot_ok himg
  removeSlot := cliPkRemoveSlot_ok himg
  getFutDrop := (cliPkGetFutVt_ok himg).drop
  getFutSize := (cliPkGetFutVt_ok himg).size
  getFutAlign := (cliPkGetFutVt_ok himg).align
  getFutPoll := (cliPkGetFutVt_ok himg).poll
  removeFutDrop := (cliPkRemoveFutVt_ok himg).drop
  removeFutSize := (cliPkRemoveFutVt_ok himg).size
  removeFutAlign := (cliPkRemoveFutVt_ok himg).align
  removeFutPoll := (cliPkRemoveFutVt_ok himg).poll

/-- End-to-end 56-byte sret bridge for `get_pre_key`: `pkGetAnsAt` on the poll's `pkAnsOf` answer
entails the kit's existential post answer (`getRel` + `preKeyGetPollOutAt`). -/
theorem pkGetAnsAt_entails_pollOut (A : RustAlloc) (b : BitVec 64)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4
    let pa := pkAnsOf PreKeyRecord.deserialize (d.get rd F0 (keyName id))
    pkGetAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr PreKeyRecord,
        ⌜kit.getRel d id ans⌝ ∗ preKeyGetPollOutAt kit out ans := by
  intro kit pa
  have hdec : ∀ e, pa = .decodeErr e → e = .invalidProtobufEncoding :=
    fun _ h => pkAnsOf_decodeErr_of_all (@preKeyDeserialize_error_eq) h
  rcases hpa : pa with r | _ | err | _
  · refine Entails.sepExists_right (.ok r) ?_
    refine ent_pure_right hpa ?_
    unfold pkGetAnsAt pkAnsAt preKeyResultAt preKeyGetPollOutAt
    dsimp only
    exact ent_pure_right trivial (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A preKeyResultAt 56 13 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .readErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    refine ent_pure_right (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl) ?_
    refine Entails.trans
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (memRegion_zero_entails_emp _))) ?_
    rw [sepConj_emp]
    exact Entails.refl _
  · refine Entails.trans
      (pkAnsAt_error_entails A preKeyResultAt 56 13 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .decodeErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    refine ent_pure_right (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl) ?_
    refine Entails.trans
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (memRegion_zero_entails_emp _))) ?_
    rw [sepConj_emp]
    exact Entails.refl _
  · refine Entails.trans
      (pkAnsAt_error_entails A preKeyResultAt 56 13 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .missing rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    refine ent_pure_right (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl) ?_
    refine Entails.trans
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (memRegion_zero_entails_emp _))) ?_
    rw [sepConj_emp]
    exact Entails.refl _

/-- End-to-end 48-byte sret bridge for `remove_pre_key`: `pkRemoveOutAt` on `pkRemoveOf` entails
the kit's existential post answer (`removeRel`, `removeUpdate` equality, and `preKeyRemovePollOutAt`). -/
theorem pkRemoveOutAt_entails_pollOut (A : RustAlloc) (b : BitVec 64)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (pid : BitVec 32)
    (s1 s2 s3 s4 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliPreKeyStoreSpec A b rd F0 pathOk pid s1 s2 s3 s4
    let res := pkRemoveOf d (keyName id) (d.get rd F0 (keyName id))
    pkRemoveOutAt A out res.1 ⊢
      ∃∗ ans : Except kit.RemoveErr Unit,
        ⌜kit.removeRel d id ans ∧ res.2 = kit.removeUpdate d id ans⌝ ∗
        preKeyRemovePollOutAt kit out ans := by
  intro kit res
  have heq := (removePreKey_eq_pkRemoveOf rd F0 d id).symm
  rcases h1 : res.1 with ⟨⟩ | ⟨⟩
  · refine Entails.trans (speAt_read_invalidState_entails A out) ?_
    refine Entails.sepExists_elim fun e => ?_
    refine Entails.sepExists_right (.error e) ?_
    refine ent_pure_right ⟨?_, ?_⟩ (Entails.refl _)
    · show (removePreKey rd F0 d id).1 = .error ()
      rw [← heq]; exact h1
    · show res.2 = (removePreKey rd F0 d id).2
      rw [← heq]
  · refine Entails.sepExists_right (.ok ()) ?_
    refine ent_pure_right ⟨?_, ?_⟩ (Entails.refl _)
    · show (removePreKey rd F0 d id).1 = .ok ()
      rw [← heq]; exact h1
    · show res.2 = (removePreKey rd F0 d id).2
      rw [← heq]

/-! ## `SignedPreKeyFiles` (`cliSignedPreKeyStoreSpec`) -/

structure CliSpkInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (sid : BitVec 32) (d : DirGhost) : Prop where
  nameOk : PkNameOk pathOk d sid
  sizeOk : PkSizeOk rd F0 d sid

def cliSpkStoreAt (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32) (self : BitVec 64) (d : DirGhost) :
    SepProp :=
  ⌜CliSpkInv rd F0 pathOk sid d⌝ ∗ dirAt A self d

/-- Concrete `SignedPreKeyStoreSpec` for `SignedPreKeyFiles` at key `sid` and initial files `F0`
(88-byte sret, missing-id SPE index `14`). -/
def cliSignedPreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (getShimStk getPollStk : Nat) : SignedPreKeyStoreSpec A b where
  spk_vt := b + cliSpkVtOff
  SpkState := DirGhost
  storeAt := cliSpkStoreAt A rd F0 pathOk sid
  idOk := fun id => id = sid
  envOk := fun f => f = F0
  fdsOk := fun fs => FdsGe3Closed fs
  GetErr := CliGetErr
  getErr := cliGetErrSpec A 14
  getRel := fun d id ans =>
    cliGetAnsRel (pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id))) ans
  getShimOff := cliSpkGetShimOff
  getFutVtOff := cliSpkGetFutVtOff
  getPollOff := cliSpkGetPollOff
  getFutDropOff := cliIdFutDropOff
  getBoxSize := 16
  getShimStack := getShimStk
  getPollStack := getPollStk
  getBoxAt := pkBoxAt
  getBoxAt_memRegion := pkBoxAt_memRegion
  getBoxSize_ne_zero := by decide
  getBoxSize_lt := by decide
  getFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

theorem cliSpk_getRel_error_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) (d : DirGhost) (id : BitVec 32) :
    (∃ e, (cliSignedPreKeyStoreSpec A b rd F0 pathOk sid s1 s2).getRel d id (.error e)) ↔
      getSignedPreKey rd F0 d id = .error () := by
  rw [getSignedPreKey_eq]
  exact cliGetAnsRel_error_iff _

theorem cliSpk_getRel_ok_iff {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) (d : DirGhost) (id : BitVec 32) (r : SignedPreKeyRecord) :
    (cliSignedPreKeyStoreSpec A b rd F0 pathOk sid s1 s2).getRel d id (.ok r) ↔
      getSignedPreKey rd F0 d id = .ok r := by
  rw [getSignedPreKey_eq]
  exact cliGetAnsRel_ok_iff _ r

theorem cliSignedPreKeyStoreSpec_quiet {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) :
    (cliSignedPreKeyStoreSpec A b rd F0 pathOk sid s1 s2).Quiet :=
  fun _ _ => by simp [cliSignedPreKeyStoreSpec, NoFsEv]

theorem cliSignedPreKeyStoreSpec_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) :
    SignedPreKeyVtablesOk img (cliSignedPreKeyStoreSpec A img.base rd F0 pathOk sid s1 s2) where
  getSlot := cliSpkGetSlot_ok himg
  getFutDrop := (cliSpkGetFutVt_ok himg).drop
  getFutSize := (cliSpkGetFutVt_ok himg).size
  getFutAlign := (cliSpkGetFutVt_ok himg).align
  getFutPoll := (cliSpkGetFutVt_ok himg).poll

/-- End-to-end 88-byte sret bridge for `get_signed_pre_key`: `spkAnsAt` (`pkAnsAt … 88 14`)
matches `spkGetPollOutAt` (`errTag`, `speErrAt (out + 8)`, `memRegion (out + 0x38) 32`) arm by arm. -/
theorem spkAnsAt_entails_pollOut (A : RustAlloc) (b : BitVec 64)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (sid : BitVec 32)
    (s1 s2 : Nat) (d : DirGhost) (id : BitVec 32) (out : BitVec 64) :
    let kit := cliSignedPreKeyStoreSpec A b rd F0 pathOk sid s1 s2
    let pa := pkAnsOf SignedPreKeyRecord.deserialize (d.get rd F0 (keyName id))
    spkAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr SignedPreKeyRecord,
        ⌜kit.getRel d id ans⌝ ∗ spkGetPollOutAt kit out ans := by
  intro kit pa
  have hdec : ∀ e, pa = .decodeErr e → e = .invalidProtobufEncoding :=
    fun _ h => pkAnsOf_decodeErr_of_all (@signedPreKeyDeserialize_error_eq) h
  rcases hpa : pa with r | _ | err | _
  · refine Entails.sepExists_right (.ok r) ?_
    refine ent_pure_right hpa ?_
    unfold spkAnsAt pkAnsAt signedPreKeyResultAt spkGetPollOutAt
    dsimp only
    exact ent_pure_right trivial (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A signedPreKeyResultAt 88 14 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .readErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A signedPreKeyResultAt 88 14 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .decodeErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A signedPreKeyResultAt 88 14 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .missing rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)

/-! ## `KyberPreKeyFiles` `get` side (`cliKpkGetSide`) -/

/-- `get_kyber_pre_key` half (`CliKpkGetSide`) of `KyberMarkFit.cliKpkStoreSpec` (88-byte sret,
missing-id SPE index `15`). -/
def cliKpkGetSide (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (_pathOk : List (BitVec 8) → Prop) (kid : BitVec 32) : CliKpkGetSide where
  RecOk := fun _ => True
  getIdOk := fun id => id = kid
  GetErr := CliGetErr
  getErr := cliGetErrSpec A 15
  getRel := fun g id ans =>
    cliGetAnsRel
      (kpkAnsOf
        (pkAnsOf KyberPreKeyRecord.deserialize (g.oneTime.get rd F0 (keyName id)))
        (pkAnsOf KyberPreKeyRecord.deserialize (g.lastResort.get rd F0 (keyName id))))
      ans

/-- Complete `KyberPreKeyStoreSpec` instantiating `cliKpkStoreSpec` with `cliKpkGetSide`. -/
abbrev cliKyberPreKeyStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (getShimStk getPollStk markShimStk markPollStk : Nat) : KyberPreKeyStoreSpec A b :=
  cliKpkStoreSpec A b rd F0 pathOk kid ksid kbk (cliKpkGetSide A rd F0 pathOk kid)
    getShimStk getPollStk markShimStk markPollStk pkBoxAt_memRegion kpkMarkBoxAt_memRegion

theorem cliKpk_getRel_error_iff {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (kid : BitVec 32)
    (g : KyberGhost) (id : BitVec 32) :
    (∃ e, (cliKpkGetSide A rd F0 pathOk kid).getRel g id (.error e)) ↔
      g.get rd F0 id = .error () := by
  rw [KyberGhost.get_eq]
  exact cliGetAnsRel_error_iff _

theorem cliKpk_getRel_ok_iff {A : RustAlloc}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (kid : BitVec 32)
    (g : KyberGhost) (id : BitVec 32) (r : KyberPreKeyRecord) :
    (cliKpkGetSide A rd F0 pathOk kid).getRel g id (.ok r) ↔
      g.get rd F0 id = .ok r := by
  rw [KyberGhost.get_eq]
  exact cliGetAnsRel_ok_iff _ r

theorem cliKpkStoreSpec_quiet {A : RustAlloc} {b : BitVec 64}
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (G : CliKpkGetSide) (s1 s2 s3 s4 : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32) :
    (cliKpkStoreSpec A b rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox).Quiet :=
  ⟨fun _ _ => by simp [cliKpkStoreSpec, NoFsEv],
    fun _ _ _ => by simp [cliKpkStoreSpec, NoFsEv]⟩

theorem cliKpkStoreSpec_vtablesOk {A : RustAlloc} {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (G : CliKpkGetSide) (s1 s2 s3 s4 : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32) :
    KyberPreKeyVtablesOk img
      (cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox) where
  getSlot := cliKpkGetSlot_ok himg
  markSlot := cliKpkMarkSlot_ok himg
  getFutDrop := (cliKpkGetFutVt_ok himg).drop
  getFutSize := (cliKpkGetFutVt_ok himg).size
  getFutAlign := (cliKpkGetFutVt_ok himg).align
  getFutPoll := (cliKpkGetFutVt_ok himg).poll
  markFutDrop := (cliKpkMarkFutVt_ok himg).drop
  markFutSize := (cliKpkMarkFutVt_ok himg).size
  markFutAlign := (cliKpkMarkFutVt_ok himg).align
  markFutPoll := (cliKpkMarkFutVt_ok himg).poll

/-- End-to-end 88-byte sret bridge for `get_kyber_pre_key`: `kpkAnsAt` (`pkAnsAt … 88 15`)
matches `kpkGetPollOutAt` (`errTag`, `speErrAt (out + 8)`, `memRegion (out + 0x38) 32`) arm by arm. -/
theorem kpkAnsAt_entails_pollOut (A : RustAlloc) (b : BitVec 64)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (s1 s2 s3 s4 : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (g : KyberGhost) (id : BitVec 32) (out : BitVec 64) :
    let G := cliKpkGetSide A rd F0 pathOk kid
    let kit := cliKpkStoreSpec A b rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
    let pa := kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (g.oneTime.get rd F0 (keyName id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (g.lastResort.get rd F0 (keyName id)))
    kpkAnsAt A out pa ⊢
      ∃∗ ans : Except kit.GetErr KyberPreKeyRecord,
        ⌜kit.getRel g id ans⌝ ∗ kpkGetPollOutAt kit out ans := by
  intro G kit pa
  have hdec : ∀ e, pa = .decodeErr e → e = .invalidProtobufEncoding :=
    fun _ h => kpkAnsOf_decodeErr_eq h
  rcases hpa : pa with r | _ | err | _
  · refine Entails.sepExists_right (.ok r) ?_
    refine ent_pure_right hpa ?_
    unfold kpkAnsAt pkAnsAt kyberPreKeyResultAt kpkGetPollOutAt
    dsimp only
    exact ent_pure_right trivial (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A kyberPreKeyResultAt 88 15 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .readErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A kyberPreKeyResultAt 88 15 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .decodeErr rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)
  · refine Entails.trans
      (pkAnsAt_error_entails A kyberPreKeyResultAt 88 15 (by decide) (by decide) (by decide)
        (fun _ => rfl) out (fun e' h' => hdec e' (hpa.trans h')) .missing rfl) ?_
    refine Entails.sepExists_elim fun e => ent_pure_left fun htag => ?_
    refine Entails.sepExists_right (.error e) ?_
    exact ent_pure_right
      (by show pkAnsErrTag? pa = some e.tag; rw [hpa, htag]; rfl)
      (Entails.refl _)

end CryptoVerification.SignalSession.Cli.KitInst
