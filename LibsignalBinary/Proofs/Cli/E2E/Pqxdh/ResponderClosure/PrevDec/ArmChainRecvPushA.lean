/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefs -- shake: keep

/-!
# Tag 7 (`receiver_chains`) 104-Byte `Chain` Move and `grow_one` Helpers

Proves 104-byte `prostChainGAt` chunk/byte move lemmas, `prostSSGQAt` `receiver_chains` open/close
identities, and `growOneChainSpecX` precondition/postcondition bridges for `PrevDec/ArmChainRecvPush.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ GenFieldQ prostSSGQAt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
open Proofs.libsignal

abbrev recvGrowOneRelOff : BitVec 64 :=
  bv% ((2 ^ 64 + (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one") -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2 ^ 64)

theorem recvGrowOne_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (contractProg b ext).fnAddr decryptPrekeyClosureName + recvGrowOneRelOff =
      (contractProg b ext).fnAddr
        "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" := by
  dsimp only [contractProg, recvGrowOneRelOff]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase, decryptPrekeyClosure_fnOff,
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
attribute [local simp, local arm64_norm ↓, local wp_norm ↓] decryptPrekeyClosure_fnOff

/-! ## 104-Byte `prostChainGAt` Move and Chunk Helpers -/

set_option maxHeartbeats 400000 in
theorem vecU8_move_bytes_rc (A : RustAlloc) (a : BitVec 64) (xs : List (BitVec 8)) :
    vecU8 A a xs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecU8 A b xs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecU8At_eq_bytes_sep_buf A a cap ptr xs]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 xs.length)) ?_
  refine Entails.sepExists_right (RustHeap.vecU8Buf A cap ptr xs) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecU8At_eq_bytes_sep_buf A b cap ptr xs]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

set_option maxHeartbeats 400000 in
theorem vecOf104_msgKey_move_bytes_rc (A : RustAlloc) (keys : List MessageKeyGenerator) (a : BitVec 64) :
    vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a keys ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 24 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b keys⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b => prostMsgKeyAt A mk b) a cap ptr keys]
  refine Entails.sepExists_right (vecHeaderBytes cap ptr (BitVec.ofNat 64 keys.length)) ?_
  refine Entails.sepExists_right (vecBuf A 104 8 (fun mk b => prostMsgKeyAt A mk b) cap ptr keys) ?_
  refine Entails.pure_right ⟨by simp [vecHeaderBytes], fun b => ?_⟩ (Entails.refl _)
  rw [← RawByteMove.vecAt_eq_bytes_sep_buf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b cap ptr keys]
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

set_option maxHeartbeats 400000 in
theorem move_bytes_pair_rc {P1 P2 : BitVec 64 → SepProp} {n1 n2 : Nat} {off : BitVec 64}
    (hoff : off = BitVec.ofNat 64 n1)
    (h1 : ∀ a : BitVec 64, P1 a ⊢
      ∃∗ bs1 : List (BitVec 8), ∃∗ H1 : SepProp,
        ⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗ (a ↦ₛ bs1) ∗ H1)
    (h2 : ∀ a : BitVec 64, P2 a ⊢
      ∃∗ bs2 : List (BitVec 8), ∃∗ H2 : SepProp,
        ⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗ (a ↦ₛ bs2) ∗ H2)
    (a : BitVec 64) :
    (P1 a ∗ P2 (a + off)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = n1 + n2 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ (P1 b ∗ P2 (b + off))⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  refine Entails.trans (sepConj_mono (h1 a) (h2 (a + off))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro bs1
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro H1
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs2
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro H2
  have hpull :
      (⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗ (a ↦ₛ bs1) ∗ H1) ∗
        (⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
          ((a + off) ↦ₛ bs2) ∗ H2) =
      ⌜bs1.length = n1 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs1) ∗ H1) ⊢ P1 b⌝ ∗
        ⌜bs2.length = n2 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs2) ∗ H2) ⊢ P2 b⌝ ∗
        ((a ↦ₛ bs1) ∗ ((a + off) ↦ₛ bs2)) ∗ (H1 ∗ H2) := by
    ac_rfl
  rw [hpull]
  apply Entails.pure_left; rintro ⟨hbs1, hmov1⟩
  apply Entails.pure_left; rintro ⟨hbs2, hmov2⟩
  have ha_off : a + off = a + BitVec.ofNat 64 bs1.length := by rw [hoff, hbs1]
  rw [ha_off, ← pointsToBytes_append]
  refine Entails.sepExists_right (bs1 ++ bs2) ?_
  refine Entails.sepExists_right (H1 ∗ H2) ?_
  refine Entails.pure_right ⟨by simp [hbs1, hbs2], fun b => ?_⟩ (Entails.refl _)
  have hb_off : b + BitVec.ofNat 64 bs1.length = b + off := by rw [hoff, hbs1]
  rw [pointsToBytes_append, hb_off]
  have hgrp :
      ((b ↦ₛ bs1) ∗ ((b + off) ↦ₛ bs2)) ∗ (H1 ∗ H2) =
      ((b ↦ₛ bs1) ∗ H1) ∗ (((b + off) ↦ₛ bs2) ∗ H2) := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono (hmov1 b) (hmov2 (b + off))

def prostCkAt_rc (A : RustAlloc) (a : BitVec 64) :
    Option (BitVec 32 × List (BitVec 8)) → SepProp
  | none => (a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 24
  | some (i, k) => vecU8 A a k ∗ ((a + 0x18#64) ↦₃₂ i) ∗ memRegion (a + 0x1c#64) 4

set_option maxHeartbeats 400000 in
theorem prostCkTailSome_move_bytes_rc (i : BitVec 32) (a : BitVec 64) :
    (((a ↦₃₂ i) ∗ memRegion (a + 4#64) 4) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 8 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ (((b ↦₃₂ i) ∗ memRegion (b + 4#64) 4))⌝ ∗
        (a ↦ₛ bs) ∗ H) := by
  rw [pointsTo32_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 4#64) 4 (by decide),
    sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pad
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpad
  have h4 : a + 4#64 = a + BitVec.ofNat 64 (unpack32 i).length := rfl
  rw [h4, ← pointsToBytes_append]
  refine Entails.sepExists_right (unpack32 i ++ pad) ?_
  refine Entails.sepExists_right emp ?_
  rw [sepConj_emp]
  refine Entails.pure_right ⟨by simp [hpad], fun b => ?_⟩ (Entails.refl _)
  rw [sepConj_emp, pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes]
  apply sepConj_mono_right
  have hm := ProofLib.pointsToBytes_entails_memRegion (b + 4#64) pad
  rwa [hpad] at hm

set_option maxHeartbeats 400000 in
theorem prostCkAt_move_bytes_rc (A : RustAlloc)
    (ck : Option (BitVec 32 × List (BitVec 8))) (a : BitVec 64) :
    prostCkAt_rc A a ck ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 32 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostCkAt_rc A b ck⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  cases ck with
  | none =>
    dsimp only [prostCkAt_rc]
    rw [pointsTo64_eq_pointsToBytes, memRegion_eq_exists_bytes (a + 8#64) 24 (by decide),
      sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro pad
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; intro hpad
    have h8 : a + 8#64 = a + BitVec.ofNat 64 (unpack64 noneCap).length := rfl
    rw [h8, ← pointsToBytes_append]
    refine Entails.sepExists_right (unpack64 noneCap ++ pad) ?_
    refine Entails.sepExists_right emp ?_
    rw [sepConj_emp]
    refine Entails.pure_right ⟨by simp [hpad], fun b => ?_⟩ (Entails.refl _)
    rw [sepConj_emp, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
    apply sepConj_mono_right
    have hm := ProofLib.pointsToBytes_entails_memRegion (b + 8#64) pad
    rwa [hpad] at hm
  | some ik =>
    rcases ik with ⟨i, k⟩
    have heq : ∀ b : BitVec 64,
        prostCkAt_rc A b (some (i, k)) =
          vecU8 A b k ∗ (((b + 0x18#64) ↦₃₂ i) ∗ memRegion ((b + 0x18#64) + 4#64) 4) := by
      intro b
      dsimp only [prostCkAt_rc]
      have e1c : b + 0x18#64 + 4#64 = b + 0x1c#64 := by rw [BitVec.add_assoc]; rfl
      rw [e1c]
    have hm := move_bytes_pair_rc (P1 := fun b => vecU8 A b k)
      (P2 := fun b => (b ↦₃₂ i) ∗ memRegion (b + 4#64) 4)
      (n1 := 24) (n2 := 8) (off := 0x18#64) rfl
      (fun b => vecU8_move_bytes_rc A b k)
      (prostCkTailSome_move_bytes_rc i) a
    simp only [show (24 : Nat) + 8 = 32 from rfl, ← heq] at hm
    exact hm

set_option maxHeartbeats 400000 in
theorem prostChainGAt_eq_parts_rc (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c =
      vecU8 A a c.srk ∗ vecU8 A (a + 0x18#64) c.priv ∗
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.keys ∗
      prostCkAt_rc A (a + 0x48#64) c.ck := by
  unfold prostChainGAt prostCkAt_rc
  have e50 : a + 0x48#64 + 8#64 = a + 0x50#64 := by rw [BitVec.add_assoc]; rfl
  have e60 : a + 0x48#64 + 0x18#64 = a + 0x60#64 := by rw [BitVec.add_assoc]; rfl
  have e64 : a + 0x48#64 + 0x1c#64 = a + 0x64#64 := by rw [BitVec.add_assoc]; rfl
  cases c.ck with
  | none =>
    dsimp only
    rw [e50]
  | some ik =>
    rcases ik with ⟨i, k⟩
    dsimp only
    rw [e60, e64]

set_option maxHeartbeats 400000 in
theorem prostChainGAt_move_bytes_rc (A : RustAlloc) (c : ChainG) (a : BitVec 64) :
    prostChainGAt A a c ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = 104 ∧ ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  have h12 := move_bytes_pair_rc
    (P1 := fun b => vecU8 A b c.srk)
    (P2 := fun b => vecU8 A b c.priv)
    (n1 := 24) (n2 := 24) (off := 0x18#64) rfl
    (fun b => vecU8_move_bytes_rc A b c.srk)
    (fun b => vecU8_move_bytes_rc A b c.priv)
  have h123 := move_bytes_pair_rc
    (P1 := fun b => vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv)
    (P2 := fun b => vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') b c.keys)
    (n1 := 48) (n2 := 24) (off := 0x30#64) rfl
    h12
    (vecOf104_msgKey_move_bytes_rc A c.keys)
  have h1234 := move_bytes_pair_rc
    (P1 := fun b => (vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
      vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys)
    (P2 := fun b => prostCkAt_rc A b c.ck)
    (n1 := 72) (n2 := 32) (off := 0x48#64) rfl
    h123
    (prostCkAt_move_bytes_rc A c.ck) a
  have heq : ∀ b : BitVec 64,
      prostChainGAt A b c =
        ((vecU8 A b c.srk ∗ vecU8 A (b + 0x18#64) c.priv) ∗
          vecOf A 104 8 (fun mk b' => prostMsgKeyAt A mk b') (b + 0x30#64) c.keys) ∗
        prostCkAt_rc A (b + 0x48#64) c.ck := by
    intro b
    rw [prostChainGAt_eq_parts_rc A b c]
    ac_rfl
  simp only [show (72 : Nat) + 32 = 104 from rfl, ← heq] at h1234
  exact h1234

set_option maxHeartbeats 400000 in
theorem prostChainGAt_move_chunks104_rc (A : RustAlloc) (a : BitVec 64) (c : ChainG) :
    prostChainGAt A a c ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ b : BitVec 64,
          (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H) ⊢ prostChainGAt A b c⌝ ∗
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ∗ H := by
  refine Entails.trans (prostChainGAt_move_bytes_rc A c a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro H
  apply Entails.pure_left; rintro ⟨hlen, hmov⟩
  obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
  rw [hchunks a]
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 (Entails.sepExists_right H ?_)))))))
  refine Entails.pure_right (fun b => ?_) (Entails.refl _)
  rw [← hchunks b]
  exact hmov b

set_option maxHeartbeats 400000 in
theorem arrayAt_prostChainGAt_move_bytes_rc (A : RustAlloc) (cs : List ChainG) (a : BitVec 64) :
    arrayAt (fun c b => prostChainGAt A b c) 104 a cs ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cs.length * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
        (a ↦ₛ bs) ∗ H := by
  induction cs generalizing a with
  | nil =>
    dsimp only [arrayAt, List.length_nil, Nat.zero_mul]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [pointsToBytes_nil, sepConj_emp]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  | cons c cs ih =>
    dsimp only [arrayAt]
    have hm := move_bytes_pair_rc
      (P1 := fun b => prostChainGAt A b c)
      (P2 := fun b => arrayAt (fun c' b' => prostChainGAt A b' c') 104 b cs)
      (n1 := 104) (n2 := cs.length * 104) (off := BitVec.ofNat 64 104) rfl
      (prostChainGAt_move_bytes_rc A c)
      ih a
    have hlen : 104 + cs.length * 104 = (c :: cs).length * 104 := by
      simp [List.length_cons, Nat.add_mul]; omega
    rw [hlen] at hm
    exact hm

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_entails_memRegion104_rc (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ⊢ memRegion a 104 := by
  rw [RawByteMove.chunks104_6QWAt_eq_pointsToBytes]
  have hm := ProofLib.pointsToBytes_entails_memRegion a (RawByteMove.bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)
  rwa [RawByteMove.bytes104Of6QW_length] at hm

set_option maxHeartbeats 400000 in
theorem memRegion104_eq_exists_chunks104_6QWAt_rc (a : BitVec 64) :
    memRegion a 104 =
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64,
        RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 := by
  rw [memRegion_eq_exists_bytes a 104 (by decide)]
  apply RawByteMove.sepProp_eq_of_entails
  · apply Entails.sepExists_elim; intro bs
    apply Entails.pure_left; intro hlen
    obtain ⟨q0, q1, q2, q3, q4, q5, w6, _, hchunks⟩ := RawByteMove.exists_bytes104Of6QW hlen
    rw [hchunks a]
    exact Entails.sepExists_right q0 (Entails.sepExists_right q1
      (Entails.sepExists_right q2 (Entails.sepExists_right q3
        (Entails.sepExists_right q4 (Entails.sepExists_right q5
          (Entails.sepExists_right w6 (Entails.refl _)))))))
  · apply Entails.sepExists_elim; intro q0
    apply Entails.sepExists_elim; intro q1
    apply Entails.sepExists_elim; intro q2
    apply Entails.sepExists_elim; intro q3
    apply Entails.sepExists_elim; intro q4
    apply Entails.sepExists_elim; intro q5
    apply Entails.sepExists_elim; intro w6
    rw [RawByteMove.chunks104_6QWAt_eq_pointsToBytes]
    exact Entails.sepExists_right _
      (Entails.pure_right (RawByteMove.bytes104Of6QW_length q0 q1 q2 q3 q4 q5 w6) (Entails.refl _))

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_read_eq_rc (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 =
      (a ↦₆₄ q0.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((a + 16#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((a + 24#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((a + 32#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((a + 40#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((a + 48#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((a + 56#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((a + 64#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((a + 72#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((a + 80#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((a + 88#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((a + 96#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_write_eq_rc (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 =
      (a ↦₆₄ q0.truncate 64) ∗ ((a + 8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((a + 16#64) ↦₆₄ q1.truncate 64) ∗ ((a + 24#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((a + 32#64) ↦₆₄ q2.truncate 64) ∗ ((a + 40#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((a + 48#64) ↦₆₄ q3.truncate 64) ∗ ((a + 56#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((a + 64#64) ↦₆₄ q4.truncate 64) ∗ ((a + 72#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((a + 80#64) ↦₆₄ q5.truncate 64) ∗ ((a + 88#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((a + 96#64) ↦₆₄ w6) := by
  unfold RawByteMove.chunks104_6QWAt pointsTo128
  have h0 (q : BitVec 128) : q.extractLsb' 0 64 = q.truncate 64 := by bv_bits
  simp only [h0, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_read_bf0_eq_rc (q : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 =
      ((q + 0xbf0#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((q + 0xbf8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((q + 0xc00#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((q + 0xc08#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((q + 0xc10#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((q + 0xc18#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((q + 0xc20#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((q + 0xc28#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((q + 0xc30#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((q + 0xc38#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((q + 0xc40#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((q + 0xc48#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((q + 0xc50#64) ↦₆₄ w6) := by
  rw [chunks104_6QWAt_read_eq_rc]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_read_a90_eq_rc (q : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 =
      ((q + 0xa90#64) ↦₆₄ q0.extractLsb' 0 64) ∗ ((q + 0xa98#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((q + 0xaa0#64) ↦₆₄ q1.extractLsb' 0 64) ∗ ((q + 0xaa8#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((q + 0xab0#64) ↦₆₄ q2.extractLsb' 0 64) ∗ ((q + 0xab8#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((q + 0xac0#64) ↦₆₄ q3.extractLsb' 0 64) ∗ ((q + 0xac8#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((q + 0xad0#64) ↦₆₄ q4.extractLsb' 0 64) ∗ ((q + 0xad8#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((q + 0xae0#64) ↦₆₄ q5.extractLsb' 0 64) ∗ ((q + 0xae8#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((q + 0xaf0#64) ↦₆₄ w6) := by
  rw [chunks104_6QWAt_read_eq_rc]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

set_option maxHeartbeats 400000 in
theorem chunks104_6QWAt_write_a90_eq_rc (q : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 =
      ((q + 0xa90#64) ↦₆₄ q0.truncate 64) ∗ ((q + 0xa98#64) ↦₆₄ q0.extractLsb' 64 64) ∗
      ((q + 0xaa0#64) ↦₆₄ q1.truncate 64) ∗ ((q + 0xaa8#64) ↦₆₄ q1.extractLsb' 64 64) ∗
      ((q + 0xab0#64) ↦₆₄ q2.truncate 64) ∗ ((q + 0xab8#64) ↦₆₄ q2.extractLsb' 64 64) ∗
      ((q + 0xac0#64) ↦₆₄ q3.truncate 64) ∗ ((q + 0xac8#64) ↦₆₄ q3.extractLsb' 64 64) ∗
      ((q + 0xad0#64) ↦₆₄ q4.truncate 64) ∗ ((q + 0xad8#64) ↦₆₄ q4.extractLsb' 64 64) ∗
      ((q + 0xae0#64) ↦₆₄ q5.truncate 64) ∗ ((q + 0xae8#64) ↦₆₄ q5.extractLsb' 64 64) ∗
      ((q + 0xaf0#64) ↦₆₄ w6) := by
  rw [chunks104_6QWAt_write_eq_rc]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## `prostSSGQAt` `receiver_chains` Open/Close and `growOneChainSpecX` Bridges -/

def prostSSGQRest (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         CryptoVerification.E2E.Record.L1GX.pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    CryptoVerification.E2E.Record.L1GX.kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

set_option maxHeartbeats 400000 in
theorem prostSSGQAt_eq_recv_sep_rest (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) :
    prostSSGQAt A ss v =
      vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
        prostSSGQRest A ss v := by
  unfold prostSSGQAt prostSSGQRest
  cases v.base.sender <;> cases v.base.pending <;> (dsimp only; ac_rfl)

set_option maxHeartbeats 400000 in
theorem prostSSGQRest_apply_recv (A : RustAlloc) (ss : BitVec 64) (v : SSGQ) (c : ChainG) :
    prostSSGQRest A ss (v.apply (.base (.recv c))) = prostSSGQRest A ss v := rfl

set_option maxHeartbeats 400000 in
theorem vecAt_recv_open_q (q : BitVec 64) (cs : List ChainG) :
    vecOf A0 104 8 (fun c a => prostChainGAt A0 a c) ((q + 0x930#64) + 0x48#64) cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e48, e50, e58, hlive, h0]
  simp only [emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem ofNat_length_eq_cap_of_eq_rc {cs : List ChainG} {cap : BitVec 64}
    (h : cs.length = cap.toNat) :
    BitVec.ofNat 64 cs.length = cap := by
  rw [h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

set_option maxHeartbeats 400000 in
theorem len_ne_cap_of_lt_rc {cs : List ChainG} {cap : BitVec 64}
    (hlt : cs.length < cap.toNat) :
    BitVec.ofNat 64 cs.length ≠ cap := by
  intro h
  have h' := congrArg BitVec.toNat h
  have hcap := cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
  omega

set_option maxHeartbeats 400000 in
theorem vecBuf_recv_full_open_rc (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A0 b' c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs
    simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (arrayAt_prostChainGAt_move_bytes_rc A0 cs ptr) ?_
    apply Entails.sepExists_elim; intro bs
    apply Entails.sepExists_elim; intro H
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    have hlive' : A0.live ptr bs.length 8 = emp := rfl
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    rw [hlive', emp_sepConj]
    exact Entails.pure_right ⟨hbs_cap, hmov⟩ (Entails.refl _)

set_option maxHeartbeats 400000 in
theorem vecBuf_recv_not_full_open_rc (cap ptr : BitVec 64) (cs : List ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else arrayAt (fun c a => prostChainGAt A0 a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (arrayAt (fun c b => prostChainGAt A0 b c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by
    intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 =
      104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]

set_option maxHeartbeats 400000 in
theorem growOne_inImage_pre_eq_q (img : Obj.Image) (q cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = q) :
    ((Stage1X.growOneChainSpecX A0).inImage img).pre
      (q + 0x978#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A0.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      stackAt q Stage1X.growOneChainStackX) := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX
  dsimp only
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have hpool : A0.pool = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  have hpure :
      (s.readReg64 .x0 = q + 0x978#64 ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) :=
    propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩,
             fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩⟩
  rw [hpure, e50, hpool, hsp, h0]
  change _ = _ ∗ (_ ∗ _ ∗ _ ∗ stackAt q (464 + Stage1X.finishGrowStackX))
  simp only [emp_sepConj, ← sepConj_assoc, pure_sepConj_pure]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem growOne_post_elim_sp_q (img : Obj.Image) (q cap ptr : BitVec 64) (cs : List ChainG)
    (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = q)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    ((Stage1X.growOneChainSpecX A0).inImage img).post
        (q + 0x978#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap') ∗ ((q + 0x980#64) ↦₆₄ p') ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        stackAt q Stage1X.growOneChainStackX := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX
  dsimp only
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  set newCap : Nat := max (2 * cap.toNat) 4
  set cap' : BitVec 64 := BitVec.ofNat 64 newCap
  have h5 : maxReceiverChains = 5 := rfl
  have hcap'_toNat : cap'.toNat = newCap := by
    dsimp only [cap', newCap]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt_cap' : cs.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have hlive : A0.live p' (newCap * 104) 8 = emp := rfl
  have hpool : A0.pool = emp := rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hlive, hpool, hsp, h0]
  change _ ⊢ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ stackAt q (464 + Stage1X.finishGrowStackX)
  simp only [emp_sepConj]
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hlt_cap', hcap'_lt, hp'⟩ ?_
  have hrem : (newCap - cap.toNat) * 104 =
      104 + (cap'.toNat - (cs.length + 1)) * 104 := by
    have : newCap - cap.toNat = 1 + (cap'.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbs_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (cs.length * 104) := by
    rw [hbs, hfull]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      p' + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hbs_eq, hrem,
      memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem vecAt_recv_push_fold_q (q cap ptr : BitVec 64) (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
        ((cap.toNat - (cs.length + 1)) * 104) ⊢
    vecOf A0 104 8 (fun c' a => prostChainGAt A0 a c') ((q + 0x930#64) + 0x48#64) (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  have hlive : A0.live ptr (cap.toNat * 104) 8 = emp := rfl
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := by
    rw [BitVec.ofNat_add]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e48, e50, e58, hlive, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]
  simp only [hne0, ↓reduceIte, emp_sepConj]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
            prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
          ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr cs ∗
          prostChainGAt A0 (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) := by
    ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

set_option maxHeartbeats 400000 in
theorem prostSSGQAt_fold_apply_recv (q cap ptr : BitVec 64) (v : SSGQ) (c : ChainG)
    (hlt : v.base.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
      arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.base.recv ∗
      prostChainGAt A0 (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
        ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
      prostSSGQRest A0 (q + 0x930#64) v) ⊢
    prostSSGQAt A0 (q + 0x930#64) (v.apply (.base (.recv c))) := by
  rw [prostSSGQAt_eq_recv_sep_rest A0 (q + 0x930#64) (v.apply (.base (.recv c))),
      prostSSGQRest_apply_recv A0 (q + 0x930#64) v c]
  dsimp only [SSGQ.apply, SSG.apply]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.base.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A0 (q + 0x930#64) v) =
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        arrayAt (fun c' a => prostChainGAt A0 a c') 104 ptr v.base.recv ∗
        prostChainGAt A0 (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104)) ∗
      prostSSGQRest A0 (q + 0x930#64) v := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_left (vecAt_recv_push_fold_q q cap ptr v.base.recv c hlt hcap_lt hptr)

set_option maxHeartbeats 400000 in
theorem memRegion104_bf0_join_rc (q : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
      memRegion (q + 0xc58#64) 24 ⊢
    memRegion (q + 0xbf0#64) 128 := by
  have h1 := chunks104_6QWAt_entails_memRegion104_rc (q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6
  have hs := memRegion_split (q + 0xbf0#64) 104 24 (by decide)
  have he : (q + 0xbf0#64) + BitVec.ofNat 64 104 = q + 0xc58#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (104 : Nat) + 24 = 128 by decide, he] at hs
  rw [hs]
  exact sepConj_mono_left h1

set_option maxHeartbeats 400000 in
theorem memRegion344_a90_split_rc (q : BitVec 64) :
    memRegion (q + 0xa90#64) 344 =
      memRegion (q + 0xa90#64) 104 ∗ memRegion (q + 0xaf8#64) 240 := by
  have hs := memRegion_split (q + 0xa90#64) 104 240 (by decide)
  have he : (q + 0xa90#64) + BitVec.ofNat 64 104 = q + 0xaf8#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (104 : Nat) + 240 = 344 by decide, he] at hs
  exact hs

set_option maxHeartbeats 400000 in
theorem memRegion344_a90_join_rc (q : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    RawByteMove.chunks104_6QWAt (q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
      memRegion (q + 0xaf8#64) 240 ⊢
    memRegion (q + 0xa90#64) 344 := by
  rw [memRegion344_a90_split_rc q]
  exact sepConj_mono_left (chunks104_6QWAt_entails_memRegion104_rc (q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6)

set_option maxHeartbeats 400000 in
theorem SepWPp_exists_left_rc {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  exact h x R hm hL

set_option maxHeartbeats 400000 in
theorem SepWPp_pure_left_rc {φ : Prop} {prog : Program} {ret : BitVec 64} {s : State}
    {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s (⌜φ⌝ ∗ F) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

/-! ## Allocator-Polymorphic `receiver_chains` Open/Close and `growOneChainSpecX` Bridges -/

set_option maxHeartbeats 400000 in
theorem vecAt_recv_open_q_ext (A : RustAlloc) (q : BitVec 64) (cs : List ChainG) :
    vecOf A 104 8 (fun c a => prostChainGAt A a c) ((q + 0x930#64) + 0x48#64) cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cs.length ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 104) 8 ∗
           arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
           memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) := by
  unfold vecOf vecAt vecHeader vecBuf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e48, e50, e58, h0]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem vecBuf_recv_full_open_rc_ext (A : RustAlloc) (cap ptr : BitVec 64) (cs : List ChainG)
    (hfull : cs.length = cap.toNat) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ H : SepProp,
        ⌜bs.length = cap.toNat * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
        (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hfull)
    subst hcs
    simp only [↓reduceIte, BitVec.toNat_ofNat]
    refine Entails.sepExists_right [] (Entails.sepExists_right emp ?_)
    rw [emp_sepConj]
    refine Entails.pure_right ⟨rfl, fun b => ?_⟩ (Entails.refl _)
    rw [pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · simp only [hcap0, ↓reduceIte]
    have hrem : (cap.toNat - cs.length) * 104 = 0 := by omega
    rw [hrem, ProofLib.memRegion_zero, sepConj_emp]
    refine Entails.trans (sepConj_mono_right (arrayAt_prostChainGAt_move_bytes_rc A cs ptr)) ?_
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro H
    have hpull :
        A.live ptr (cap.toNat * 104) 8 ∗
          (⌜bs.length = cs.length * 104 ∧
            ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
            (ptr ↦ₛ bs) ∗ H) =
        ⌜bs.length = cs.length * 104 ∧
          ∀ b : BitVec 64, ((b ↦ₛ bs) ∗ H) ⊢ arrayAt (fun c b' => prostChainGAt A b' c) 104 b cs⌝ ∗
          (A.live ptr (cap.toNat * 104) 8 ∗ (ptr ↦ₛ bs)) ∗ H := by
      ac_rfl
    rw [hpull]
    apply Entails.pure_left; rintro ⟨hbs_len, hmov⟩
    have hbs_cap : bs.length = cap.toNat * 104 := by rw [hbs_len, hfull]
    rw [← hbs_cap]
    refine Entails.sepExists_right bs (Entails.sepExists_right H ?_)
    exact Entails.pure_right ⟨rfl, hmov⟩ (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 400000 in
theorem vecBuf_recv_not_full_open_rc_ext (A : RustAlloc) (cap ptr : BitVec 64) (cs : List ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) :
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 104) 8 ∗
       arrayAt (fun c a => prostChainGAt A a c) 104 ptr cs ∗
       memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
      (A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c b => prostChainGAt A b c) 104 ptr cs ∗
        memRegion (ptr + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap.toNat - (cs.length + 1)) * 104)) := by
  have hcap0 : cap ≠ 0#64 := by
    intro h0; subst h0; simp at hlt
  simp only [hcap0, ↓reduceIte]
  have hrem : (cap.toNat - cs.length) * 104 =
      104 + (cap.toNat - (cs.length + 1)) * 104 := by
    have : cap.toNat - cs.length = 1 + (cap.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      ptr + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        ptr + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hrem, memRegion_split (ptr + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]

set_option maxHeartbeats 400000 in
theorem growOne_inImage_pre_eq_q_ext (A : RustAlloc) (img : Obj.Image) (q cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (s : State) (hsp : s.sp = q) :
    ((Stage1X.growOneChainSpecX A).inImage img).pre
      (q + 0x978#64, cap, ptr, bs) s =
    ⌜(bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧
        ptr ≠ 0#64 ∧ 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      (if cap = 0#64 then emp else A.live ptr bs.length 8 ∗ (ptr ↦ₛ bs)) ∗
      A.pool ∗
      stackAt q Stage1X.growOneChainStackX) := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX
  dsimp only
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  have hpure :
      (s.readReg64 .x0 = q + 0x978#64 ∧ bs.length = cap.toNat * 104 ∧ ptr ≠ 0 ∧
        max (2 * cap.toNat) 4 * 104 + 8 ≤ 2 ^ 63) =
      (bs.length = cap.toNat * 104 ∧ s.readReg64 .x0 = q + 0x978#64 ∧ ptr ≠ 0#64 ∧
        8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63) :=
    propext ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩,
             fun ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3, by omega⟩⟩
  rw [hpure, e50, hsp, h0]
  change _ = _ ∗ (_ ∗ _ ∗ _ ∗ A.pool ∗ stackAt q (464 + Stage1X.finishGrowStackX))
  simp only [← sepConj_assoc, pure_sepConj_pure]
  ac_rfl

set_option maxHeartbeats 400000 in
theorem growOne_post_elim_sp_q_ext (A : RustAlloc) (img : Obj.Image) (q cap ptr : BitVec 64)
    (cs : List ChainG) (bs : List (BitVec 8)) (s_pre sf : State)
    (hsp : s_pre.sp = q)
    (hfull : cs.length = cap.toNat)
    (hlt5 : cs.length < maxReceiverChains)
    (hbs : bs.length = cap.toNat * 104) :
    ((Stage1X.growOneChainSpecX A).inImage img).post
        (q + 0x978#64, cap, ptr, bs) s_pre sf ⊢
      ⌜sf.trace = s_pre.trace⌝ ∗
      ∃∗ cap' : BitVec 64, ∃∗ p' : BitVec 64,
        ⌜cs.length < cap'.toNat ∧ cap'.toNat * 104 < 2 ^ 63 ∧ p' ≠ 0#64⌝ ∗
        ((q + 0x978#64) ↦₆₄ cap') ∗ ((q + 0x980#64) ↦₆₄ p') ∗
        A.live p' (cap'.toNat * 104) 8 ∗
        (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 cs.length * 104#64) 104 ∗
        memRegion (p' + BitVec.ofNat 64 ((cs.length + 1) * 104))
          ((cap'.toNat - (cs.length + 1)) * 104) ∗
        A.pool ∗
        stackAt q Stage1X.growOneChainStackX := by
  unfold Spec.inImage Stage1X.growOneChainSpecX Stage1X.growOne104SpecX
  dsimp only
  apply Entails.pure_left; intro htr
  refine Entails.pure_right htr ?_
  apply Entails.sepExists_elim; intro p'
  set newCap : Nat := max (2 * cap.toNat) 4
  set cap' : BitVec 64 := BitVec.ofNat 64 newCap
  have h5 : maxReceiverChains = 5 := rfl
  have hcap'_toNat : cap'.toNat = newCap := by
    dsimp only [cap', newCap]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt_cap' : cs.length < cap'.toNat := by omega
  have hcap'_lt : cap'.toNat * 104 < 2 ^ 63 := by omega
  refine Entails.sepExists_right cap' (Entails.sepExists_right p' ?_)
  have e50 : q + 0x978#64 + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have h0 : (0 : BitVec 64) = 0#64 := rfl
  rw [e50, hsp, h0]
  change _ ⊢ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ stackAt q (464 + Stage1X.finishGrowStackX)
  apply Entails.pure_left; intro hp'
  refine Entails.pure_right ⟨hlt_cap', hcap'_lt, hp'⟩ ?_
  have hlive_eq : A.live p' (newCap * 104) 8 = A.live p' (cap'.toNat * 104) 8 := by
    rw [hcap'_toNat]
  have hrem : (newCap - cap.toNat) * 104 =
      104 + (cap'.toNat - (cs.length + 1)) * 104 := by
    have : newCap - cap.toNat = 1 + (cap'.toNat - (cs.length + 1)) := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hbs_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (cs.length * 104) := by
    rw [hbs, hfull]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have hoff :
      p' + BitVec.ofNat 64 (cs.length * 104) + BitVec.ofNat 64 104 =
        p' + BitVec.ofNat 64 ((cs.length + 1) * 104) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hlive_eq, hbs_eq, hrem,
      memRegion_split (p' + BitVec.ofNat 64 (cs.length * 104)) 104 _ (by omega),
      hoff, hmul]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
theorem vecAt_recv_push_fold_q_ext (A : RustAlloc) (q cap ptr : BitVec 64)
    (cs : List ChainG) (c : ChainG)
    (hlt : cs.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
        ((cap.toNat - (cs.length + 1)) * 104) ⊢
    vecOf A 104 8 (fun c' a => prostChainGAt A a c') ((q + 0x930#64) + 0x48#64) (cs ++ [c]) := by
  have hne0 : cap ≠ 0 := by
    intro h0; subst h0; simp at hlt
  unfold vecOf vecAt vecHeader vecBuf
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have e48 : (q + 0x930#64) + 0x48#64 = q + 0x978#64 := by rw [BitVec.add_assoc]; rfl
  have e50 : (q + 0x978#64) + 8#64 = q + 0x980#64 := by rw [BitVec.add_assoc]; rfl
  have e58 : (q + 0x978#64) + 16#64 = q + 0x988#64 := by rw [BitVec.add_assoc]; rfl
  have hlen_app : (cs ++ [c]).length = cs.length + 1 := by simp
  have hlen_bv : BitVec.ofNat 64 (cs.length + 1) = BitVec.ofNat 64 cs.length + 1#64 := by
    rw [BitVec.ofNat_add]
  have hmul : BitVec.ofNat 64 (cs.length * 104) = BitVec.ofNat 64 cs.length * 104#64 := by
    rw [BitVec.ofNat_mul]
  have h0 : (ptr ≠ (0 : BitVec 64)) = (ptr ≠ 0#64) := rfl
  rw [e48, e50, e58, hlen_app, hlen_bv, arrayAt_concat, hmul, h0]
  simp only [hne0, ↓reduceIte]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64))) ∗
        (⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (A.live ptr (cap.toNat * 104) 8 ∗
            (arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
              prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c) ∗
            memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
              ((cap.toNat - (cs.length + 1)) * 104))) =
      ⌜cs.length + 1 ≤ cap.toNat ∧ cap.toNat * 104 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
          ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 cs.length + 1#64)) ∗
          A.live ptr (cap.toNat * 104) 8 ∗
          arrayAt (fun c' a => prostChainGAt A a c') 104 ptr cs ∗
          prostChainGAt A (ptr + BitVec.ofNat 64 cs.length * 104#64) c ∗
          memRegion (ptr + BitVec.ofNat 64 ((cs.length + 1) * 104))
            ((cap.toNat - (cs.length + 1)) * 104)) := by
    ac_rfl
  rw [hgrp]
  exact Entails.pure_right ⟨by omega, hcap_lt, hptr⟩ (Entails.refl _)

set_option maxHeartbeats 400000 in
theorem prostSSGQAt_fold_apply_recv_ext (A : RustAlloc) (q cap ptr : BitVec 64)
    (v : SSGQ) (c : ChainG)
    (hlt : v.base.recv.length < cap.toNat) (hcap_lt : cap.toNat * 104 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) :
    (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
      ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
      A.live ptr (cap.toNat * 104) 8 ∗
      arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
      prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
      memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
        ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
      prostSSGQRest A (q + 0x930#64) v) ⊢
    prostSSGQAt A (q + 0x930#64) (v.apply (.base (.recv c))) := by
  rw [prostSSGQAt_eq_recv_sep_rest A (q + 0x930#64) (v.apply (.base (.recv c))),
      prostSSGQRest_apply_recv A (q + 0x930#64) v c]
  dsimp only [SSGQ.apply, SSG.apply]
  have hgrp :
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
        prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A (q + 0x930#64) v) =
      (((q + 0x978#64) ↦₆₄ cap) ∗ ((q + 0x980#64) ↦₆₄ ptr) ∗
        ((q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr (cap.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr v.base.recv ∗
        prostChainGAt A (ptr + BitVec.ofNat 64 v.base.recv.length * 104#64) c ∗
        memRegion (ptr + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap.toNat - (v.base.recv.length + 1)) * 104)) ∗
      prostSSGQRest A (q + 0x930#64) v := by
    ac_rfl
  rw [hgrp]
  exact sepConj_mono_left (vecAt_recv_push_fold_q_ext A q cap ptr v.base.recv c hlt hcap_lt hptr)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
