/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneChains
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Clone Segment of `session_message_decrypt_signal` (`SegClone`)

Proves `segClone_ok : SegCloneSpec img C A ctl parse S abs` (`+0x1a8 → +0x69c / +0x7e4`) in
`session_message_decrypt_signal` (`0x3a4a8`), both in-image and under `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Extern hooks, callee address bridges, and panic tails -/

private theorem segClone_shim_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
      sessionShimSpec :=
  hA.shim_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

private theorem segClone_alloc_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

private theorem segClone_memcpy_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at msgDecryptName (num% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

private theorem segClone_panic_at_handle_error {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext msgDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

private theorem fnAddr_msgDecrypt_to_chainClone {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")) =
      (tripleRatchetProgAtExt b ext).fnAddr chainCloneName := by
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff msgDecryptName)) + bv% (2 ^ 64 - 8252) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainCloneName)
  rw [libsignalSessionCode_fnOff_sym_3a4a8, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")]
  bv_omega

private theorem segClone_chainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcc : ChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")))
      (chainCloneSpec A) := by
  rwa [fnAddr_msgDecrypt_to_chainClone]

private theorem segClone_senderChainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hscc : SenderChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")))
      (senderChainCloneSpec A) := by
  rwa [fnAddr_msgDecrypt_to_chainClone]

private abbrev clonePanicPost (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R)

private theorem onPanic_of_allocFailed {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  simpa only [recordDecryptSpec, Spec.inImage, sepConj_assoc] using
    allowPanic_panicked ⟨Or.inr (Or.inr halloc.1), halloc.2⟩ hm

private theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

private theorem segClone_panic_0x25f8 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x25f8#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x25f8 img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

private theorem segClone_panic_0x2604 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2604#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x2604 img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

private theorem segClone_panic_0x2610 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2610#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x2610 img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

private theorem segClone_panic_0x261c {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x261c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x261c img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

private theorem segClone_panic_0x2628 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2628#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x2628 img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

private theorem segClone_panic_0x2634 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2634#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_panic_0x2634 img C A ctl S ext ret Q x s0 s P R hpc hrun htrace

/-! ## Arithmetic, byte-slice, and `Vec<u8>` helpers -/

private theorem srk_length_pos {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 0 < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons _ _ => exact Nat.succ_pos _

private theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

private theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

private theorem cap_add_one_ne_zero {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add] at ht
  change (cap.toNat + 1) % 2 ^ 64 = 0 at ht
  rw [Nat.mod_eq_of_lt (by omega)] at ht
  omega

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact cap_add_one_ne_zero hlt

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem segClone_pure_eq_emp {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  rw [propext ⟨fun _ => trivial, fun _ => h⟩]; simp

private theorem vecU8Buf_pure_extract (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.pure_left; intro hp
    exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
  · exact Entails.pure_left fun _ => Entails.refl _

private theorem vecU8At_eq_of_nil (A : RustAlloc) (a cap ptr : BitVec 64) :
    vecU8At A a cap ptr [] =
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A cap ptr [] := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  apply ProofLib.sepProp_eq_of_entails
  · conv => lhs; rw [vecU8Buf_pure_extract]
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨_, hcap, hptr⟩
    apply Entails.pure_right ⟨hcap, hptr⟩
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    exact Entails.refl _
  · apply Entails.pure_left; intro _
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc]
    exact Entails.refl _

private theorem vecU8At_eq_of_pos (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
  unfold vecU8At vecHeader
  apply ProofLib.sepProp_eq_of_entails
  · rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    simp only [hne, ↓reduceIte]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    have hcomm :
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) =
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _
  · apply Entails.pure_left; rintro ⟨hlen, hcap_lt, hptr⟩
    have hne : cap ≠ 0 := by
      intro h0; rw [h0] at hlen; change bs.length ≤ 0 at hlen; omega
    rw [sepConj_pure_left_comm]
    apply Entails.pure_right ⟨hlen, hcap_lt, hptr⟩
    simp only [hne, ↓reduceIte]
    have hcomm :
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
        (((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
      ac_rfl
    rw [hcomm]; exact Entails.refl _

private theorem vecGhostAt_eq_of_nil (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g a =
      ⌜g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr [] := by
  unfold vecGhostAt
  rw [hnil, vecU8At_eq_of_nil]

private theorem vecGhostAt_eq_of_pos (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) :=
  vecU8At_eq_of_pos A a g.cap g.ptr g.bytes hpos

private theorem vecU8Buf_nil_eq (A : RustAlloc) :
    vecU8Buf A 0#64 1#64 [] = emp := by
  unfold vecU8Buf
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

private theorem vecU8Buf_pos_eq (A : RustAlloc) (ptr' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hptr' : ptr' ≠ 0#64) :
    vecU8Buf A (BitVec.ofNat 64 bs.length) ptr' bs =
      A.live ptr' bs.length 1 ∗ (ptr' ↦ₛ bs) := by
  unfold vecU8Buf
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [htoNat] at ht; change bs.length = 0 at ht; omega
  have hptr_ne : ptr' ≠ 0 := hptr'
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hlt, hptr_ne⟩
    simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
    exact Entails.refl _

private theorem stackAt_root_eq_chainClone (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
        stackAt sp chainCloneStack := by
  have h := stackAt_split_bottom sp chainCloneStack (rootStack - chainCloneStack) (by decide)
  rwa [show chainCloneStack + (rootStack - chainCloneStack) = rootStack by decide] at h

private theorem stackAt_chainClone_eq_alloc (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack 208 (by decide)
  rwa [show allocHookStack + 208 = chainCloneStack by decide] at h

/-! ## Stack frame, spill slots, and field decomposition lemmas -/

private theorem elim_region8 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 8 + rem) (hb : b' = b + 8#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 64, (memRegion b' rem ∗ (b ↦₆₄ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₆₄ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₆₄ v) ∗ F by ac_rfl]
  exact h v

private theorem elim_region4 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 4 + rem) (hb : b' = b + 4#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 32, (memRegion b' rem ∗ (b ↦₃₂ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₃₂ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₃₂ v) ∗ F by ac_rfl]
  exact h v

private theorem elim_region1 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 1 + rem) (hb : b' = b + 1#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 8, (memRegion b' rem ∗ (b ↦₈ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₈ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₈ v) ∗ F by ac_rfl]
  exact h v

private theorem elim_region_skip {b b' : BitVec 64} {N n rem : Nat} {F Q : SepProp}
    (hN : N = n + rem) (hb : b' = b + BitVec.ofNat 64 n) (hle : N ≤ 2 ^ 64)
    (h : (memRegion b' rem ∗ memRegion b n ∗ F) ⊢ Q) :
    (memRegion b N ∗ F) ⊢ Q := by
  rw [memRegion_split' hN hb hle]
  rw [show (memRegion b n ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ memRegion b n ∗ F by ac_rfl]
  exact h

private theorem elim_region96_6Q {b b' : BitVec 64} {N rem : Nat} {F Q : SepProp}
    (hN : N = 96 + rem) (hb : b' = b + 96#64) (hle : N ≤ 2 ^ 64)
    (h : ∀ q0 q1 q2 q3 q4 q5 : BitVec 128,
      (memRegion b' rem ∗ chunks96_6QAt b q0 q1 q2 q3 q4 q5 ∗ F) ⊢ Q) :
    (memRegion b N ∗ F) ⊢ Q := by
  rw [memRegion_split' hN hb hle, memRegion_96_eq_exists_chunks96_6QAt]
  simp only [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro q0
  apply Entails.sepExists_elim; intro q1
  apply Entails.sepExists_elim; intro q2
  apply Entails.sepExists_elim; intro q3
  apply Entails.sepExists_elim; intro q4
  apply Entails.sepExists_elim; intro q5
  rw [show (chunks96_6QAt b q0 q1 q2 q3 q4 q5 ∗ memRegion b' rem) ∗ F =
        memRegion b' rem ∗ chunks96_6QAt b q0 q1 q2 q3 q4 q5 ∗ F by ac_rfl]
  exact h q0 q1 q2 q3 q4 q5

/-- Values of the 17 stack spill slots in `sp .. sp + 0x80`. -/
private structure SpillVals where
  v00 : BitVec 64
  v08 : BitVec 64
  v14 : BitVec 32
  v18 : BitVec 64
  v24 : BitVec 32
  v28 : BitVec 32
  v2c : BitVec 32
  v30 : BitVec 64
  v3c : BitVec 32
  v40 : BitVec 64
  v48 : BitVec 64
  v54 : BitVec 32
  v58 : BitVec 64
  v60 : BitVec 64
  v68 : BitVec 64
  v70 : BitVec 64
  v78 : BitVec 64

/-- Spatial layout of the 128-byte spill area `sp .. sp + 0x80`. -/
private def spillSlotsAt (sp : BitVec 64)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) : SepProp :=
  (sp ↦₆₄ v00) ∗ ((sp + 0x8#64) ↦₆₄ v08) ∗
  memRegion (sp + 0x10#64) 4 ∗ ((sp + 0x14#64) ↦₃₂ v14) ∗
  ((sp + 0x18#64) ↦₆₄ v18) ∗
  memRegion (sp + 0x20#64) 4 ∗ ((sp + 0x24#64) ↦₃₂ v24) ∗
  ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗
  ((sp + 0x30#64) ↦₆₄ v30) ∗
  memRegion (sp + 0x38#64) 4 ∗ ((sp + 0x3c#64) ↦₃₂ v3c) ∗
  ((sp + 0x40#64) ↦₆₄ v40) ∗ ((sp + 0x48#64) ↦₆₄ v48) ∗
  memRegion (sp + 0x50#64) 4 ∗ ((sp + 0x54#64) ↦₃₂ v54) ∗
  ((sp + 0x58#64) ↦₆₄ v58) ∗ ((sp + 0x60#64) ↦₆₄ v60) ∗
  ((sp + 0x68#64) ↦₆₄ v68) ∗ ((sp + 0x70#64) ↦₆₄ v70) ∗
  ((sp + 0x78#64) ↦₆₄ v78)

private theorem memRegion_0x80_entails_spillSlotsAt (sp : BitVec 64) :
    memRegion sp 0x80 ⊢
      ∃∗ sv : SpillVals,
        spillSlotsAt sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
          sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 := by
  rw [← sepConj_emp (memRegion sp 0x80)]
  refine elim_region8 (b' := sp + 0x8#64) (rem := 120) rfl rfl (by decide) fun v00 => ?_
  refine elim_region8 (b' := sp + 0x10#64) (rem := 112) rfl (by bv_arith) (by decide) fun v08 => ?_
  refine elim_region_skip (b' := sp + 0x14#64) (n := 4) (rem := 108) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x18#64) (rem := 104) rfl (by bv_arith) (by decide) fun v14 => ?_
  refine elim_region8 (b' := sp + 0x20#64) (rem := 96) rfl (by bv_arith) (by decide) fun v18 => ?_
  refine elim_region_skip (b' := sp + 0x24#64) (n := 4) (rem := 92) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x28#64) (rem := 88) rfl (by bv_arith) (by decide) fun v24 => ?_
  refine elim_region4 (b' := sp + 0x2c#64) (rem := 84) rfl (by bv_arith) (by decide) fun v28 => ?_
  refine elim_region4 (b' := sp + 0x30#64) (rem := 80) rfl (by bv_arith) (by decide) fun v2c => ?_
  refine elim_region8 (b' := sp + 0x38#64) (rem := 72) rfl (by bv_arith) (by decide) fun v30 => ?_
  refine elim_region_skip (b' := sp + 0x3c#64) (n := 4) (rem := 68) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x40#64) (rem := 64) rfl (by bv_arith) (by decide) fun v3c => ?_
  refine elim_region8 (b' := sp + 0x48#64) (rem := 56) rfl (by bv_arith) (by decide) fun v40 => ?_
  refine elim_region8 (b' := sp + 0x50#64) (rem := 48) rfl (by bv_arith) (by decide) fun v48 => ?_
  refine elim_region_skip (b' := sp + 0x54#64) (n := 4) (rem := 44) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0x58#64) (rem := 40) rfl (by bv_arith) (by decide) fun v54 => ?_
  refine elim_region8 (b' := sp + 0x60#64) (rem := 32) rfl (by bv_arith) (by decide) fun v58 => ?_
  refine elim_region8 (b' := sp + 0x68#64) (rem := 24) rfl (by bv_arith) (by decide) fun v60 => ?_
  refine elim_region8 (b' := sp + 0x70#64) (rem := 16) rfl (by bv_arith) (by decide) fun v68 => ?_
  refine elim_region8 (b' := sp + 0x78#64) (rem := 8) rfl (by bv_arith) (by decide) fun v70 => ?_
  refine elim_region8 (b' := sp + 0x80#64) (rem := 0) rfl (by bv_arith) (by decide) fun v78 => ?_
  rw [ProofLib.memRegion_zero]
  refine Entails.sepExists_right
    ⟨v00, v08, v14, v18, v24, v28, v2c, v30, v3c, v40, v48, v54, v58, v60, v68, v70, v78⟩ ?_
  unfold spillSlotsAt
  exact Entails.of_eq (by ac_rfl)

private theorem spillSlotsAt_entails_memRegion_0x80 (sp : BitVec 64)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) :
    spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78 ⊢
      memRegion sp 0x80 := by
  unfold spillSlotsAt
  rw [memRegion_split' (b := sp) (b' := sp + 0x8#64) (n := 8) (k := 120) rfl rfl (by decide),
      memRegion_split' (b := sp + 0x8#64) (b' := sp + 0x10#64) (n := 8) (k := 112) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x10#64) (b' := sp + 0x14#64) (n := 4) (k := 108) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x14#64) (b' := sp + 0x18#64) (n := 4) (k := 104) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x18#64) (b' := sp + 0x20#64) (n := 8) (k := 96) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x20#64) (b' := sp + 0x24#64) (n := 4) (k := 92) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x24#64) (b' := sp + 0x28#64) (n := 4) (k := 88) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x28#64) (b' := sp + 0x2c#64) (n := 4) (k := 84) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x2c#64) (b' := sp + 0x30#64) (n := 4) (k := 80) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x30#64) (b' := sp + 0x38#64) (n := 8) (k := 72) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x38#64) (b' := sp + 0x3c#64) (n := 4) (k := 68) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x3c#64) (b' := sp + 0x40#64) (n := 4) (k := 64) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x40#64) (b' := sp + 0x48#64) (n := 8) (k := 56) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x48#64) (b' := sp + 0x50#64) (n := 8) (k := 48) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x50#64) (b' := sp + 0x54#64) (n := 4) (k := 44) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x54#64) (b' := sp + 0x58#64) (n := 4) (k := 40) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x58#64) (b' := sp + 0x60#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x60#64) (b' := sp + 0x68#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x68#64) (b' := sp + 0x70#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x70#64) (b' := sp + 0x78#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide)]
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (Entails.refl _) <|
    sepConj_mono (pointsTo32_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    sepConj_mono (pointsTo64_entails_memRegion _ _) <|
    pointsTo64_entails_memRegion _ _

private theorem memRegion_0x80_0x20_entails (sp : BitVec 64) :
    memRegion (sp + 0x80#64) 0x20 ⊢
      ∃∗ v80 : BitVec 64, ∃∗ v88 : BitVec 64, ∃∗ v90 : BitVec 64, ∃∗ v9c : BitVec 32,
        ((sp + 0x80#64) ↦₆₄ v80) ∗ ((sp + 0x88#64) ↦₆₄ v88) ∗ ((sp + 0x90#64) ↦₆₄ v90) ∗
        memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ v9c) := by
  rw [← sepConj_emp (memRegion (sp + 0x80#64) 0x20)]
  refine elim_region8 (b' := sp + 0x88#64) (rem := 24) rfl (by bv_arith) (by decide) fun v80 => ?_
  refine elim_region8 (b' := sp + 0x90#64) (rem := 16) rfl (by bv_arith) (by decide) fun v88 => ?_
  refine elim_region8 (b' := sp + 0x98#64) (rem := 8) rfl (by bv_arith) (by decide) fun v90 => ?_
  refine elim_region_skip (b' := sp + 0x9c#64) (n := 4) (rem := 4) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0xa0#64) (rem := 0) rfl (by bv_arith) (by decide) fun v9c => ?_
  rw [ProofLib.memRegion_zero]
  refine Entails.sepExists_right v80 (Entails.sepExists_right v88
    (Entails.sepExists_right v90 (Entails.sepExists_right v9c ?_)))
  exact Entails.of_eq (by ac_rfl)

private theorem memRegion_0x5b0_0x40_entails (sp : BitVec 64) :
    memRegion (sp + 0x5b0#64) 0x40 ⊢
      ∃∗ v5b0 : BitVec 64, ∃∗ v5bc : BitVec 8, ∃∗ v5c0 : BitVec 64,
      ∃∗ v5c8 : BitVec 64, ∃∗ v5d0 : BitVec 64, ∃∗ v5d8 : BitVec 64,
      ∃∗ v5e0 : BitVec 64, ∃∗ v5e8 : BitVec 64,
        ((sp + 0x5b0#64) ↦₆₄ v5b0) ∗ memRegion (sp + 0x5b8#64) 4 ∗
        ((sp + 0x5bc#64) ↦₈ v5bc) ∗ memRegion (sp + 0x5bd#64) 3 ∗
        ((sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((sp + 0x5c8#64) ↦₆₄ v5c8) ∗
        ((sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((sp + 0x5d8#64) ↦₆₄ v5d8) ∗
        ((sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((sp + 0x5e8#64) ↦₆₄ v5e8) := by
  rw [← sepConj_emp (memRegion (sp + 0x5b0#64) 0x40)]
  refine elim_region8 (b' := sp + 0x5b8#64) (rem := 56) rfl (by bv_arith) (by decide) fun v5b0 => ?_
  refine elim_region_skip (b' := sp + 0x5bc#64) (n := 4) (rem := 52) rfl (by bv_arith) (by decide) ?_
  refine elim_region1 (b' := sp + 0x5bd#64) (rem := 51) rfl (by bv_arith) (by decide) fun v5bc => ?_
  refine elim_region_skip (b' := sp + 0x5c0#64) (n := 3) (rem := 48) rfl (by bv_arith) (by decide) ?_
  refine elim_region8 (b' := sp + 0x5c8#64) (rem := 40) rfl (by bv_arith) (by decide) fun v5c0 => ?_
  refine elim_region8 (b' := sp + 0x5d0#64) (rem := 32) rfl (by bv_arith) (by decide) fun v5c8 => ?_
  refine elim_region8 (b' := sp + 0x5d8#64) (rem := 24) rfl (by bv_arith) (by decide) fun v5d0 => ?_
  refine elim_region8 (b' := sp + 0x5e0#64) (rem := 16) rfl (by bv_arith) (by decide) fun v5d8 => ?_
  refine elim_region8 (b' := sp + 0x5e8#64) (rem := 8) rfl (by bv_arith) (by decide) fun v5e0 => ?_
  refine elim_region8 (b' := sp + 0x5f0#64) (rem := 0) rfl (by bv_arith) (by decide) fun v5e8 => ?_
  rw [ProofLib.memRegion_zero]
  refine Entails.sepExists_right v5b0 (Entails.sepExists_right v5bc
    (Entails.sepExists_right v5c0 (Entails.sepExists_right v5c8
      (Entails.sepExists_right v5d0 (Entails.sepExists_right v5d8
        (Entails.sepExists_right v5e0 (Entails.sepExists_right v5e8 ?_)))))))
  exact Entails.of_eq (by ac_rfl)

private theorem memRegion_0x5f0_0x6b0_eq (sp : BitVec 64) :
    memRegion (sp + 0x5f0#64) 0x6b0 =
      memRegion (sp + 0x5f0#64) 104 ∗
      memRegion (sp + 0x658#64) 0x4e8 ∗
      memRegion (sp + 0xb40#64) 96 ∗
      memRegion (sp + 0xba0#64) 0x100 := by
  rw [memRegion_split' (b := sp + 0x5f0#64) (b' := sp + 0x658#64) (n := 104) (k := 1608) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x658#64) (b' := sp + 0xb40#64) (n := 0x4e8) (k := 352) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xb40#64) (b' := sp + 0xba0#64) (n := 96) (k := 0x100) rfl (by bv_arith) (by decide)]

private theorem chunks96_6QAt_entails_memRegion (base : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt base q0 q1 q2 q3 q4 q5 ⊢ memRegion base 96 := by
  rw [chunks96_6QAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion base (bytes96Of6Q q0 q1 q2 q3 q4 q5)
  rwa [bytes96Of6Q_length] at h

private theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ v : BitVec 32, bs = unpack32 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;>
    try (simp at h)
  refine ⟨b3 ++ b2 ++ b1 ++ b0, ?_⟩
  simp only [unpack32, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

private theorem exists_unpack32_pair_of_length_8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w0 w1 : BitVec 32,
      bs = unpack32 w0 ++ unpack32 w1 ∧
      ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) := by
  have h0 : (bs.take 4).length = 4 := by simp [h]
  have h1 : (bs.drop 4).length = 4 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_unpack32_of_length_4 h0
  obtain ⟨w1, hw1⟩ := exists_unpack32_of_length_4 h1
  have hbs : bs = unpack32 w0 ++ unpack32 w1 := by
    rw [← hw0, ← hw1, List.take_append_drop]
  refine ⟨w0, w1, hbs, fun a => ?_⟩
  conv => lhs; rw [hbs]
  rw [pointsToBytes_append, unpack32_length, ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]

private theorem exists_tail24_decomp {bs : List (BitVec 8)} (h : bs.length = 24) :
    ∃ (w0 w1 : BitVec 32) (d2 : BitVec 64) (w3 w4 : BitVec 32),
      bs = unpack32 w0 ++ unpack32 w1 ++ unpack64 d2 ++ unpack32 w3 ++ unpack32 w4 ∧
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₃₂ w1) ∗ ((a + 8#64) ↦₆₄ d2) ∗
          ((a + 16#64) ↦₃₂ w3) ∗ ((a + 20#64) ↦₃₂ w4) := by
  have h0 : (bs.take 4).length = 4 := by simp [h]
  have h1 : ((bs.drop 4).take 4).length = 4 := by simp [h]
  have h2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h3 : ((bs.drop 16).take 4).length = 4 := by simp [h]
  have h4 : (bs.drop 20).length = 4 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_unpack32_of_length_4 h0
  obtain ⟨w1, hw1⟩ := exists_unpack32_of_length_4 h1
  obtain ⟨d2, hd2⟩ := exists_unpack64_of_length_8 h2
  obtain ⟨w3, hw3⟩ := exists_unpack32_of_length_4 h3
  obtain ⟨w4, hw4⟩ := exists_unpack32_of_length_4 h4
  have hbs : bs = unpack32 w0 ++ unpack32 w1 ++ unpack64 d2 ++ unpack32 w3 ++ unpack32 w4 := by
    rw [← hw0, ← hw1, ← hd2, ← hw3, ← hw4]
    simp only [List.append_assoc]
    have s3 : (bs.drop 16).take 4 ++ bs.drop 20 = bs.drop 16 := by
      have := List.take_append_drop 4 (bs.drop 16); rwa [List.drop_drop] at this
    have s2 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
      have := List.take_append_drop 8 (bs.drop 8); rwa [List.drop_drop] at this
    have s1 : (bs.drop 4).take 4 ++ bs.drop 8 = bs.drop 4 := by
      have := List.take_append_drop 4 (bs.drop 4); rwa [List.drop_drop] at this
    rw [s3, s2, s1, List.take_append_drop]
  refine ⟨w0, w1, d2, w3, w4, hbs, fun a => ?_⟩
  conv => lhs; rw [hbs]
  simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack64_length,
    ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  have ha4 : a + BitVec.ofNat 64 4 = a + 4#64 := rfl
  have ha8 : a + 4#64 + BitVec.ofNat 64 4 = a + 8#64 := by bv_arith
  have ha16 : a + 8#64 + BitVec.ofNat 64 8 = a + 16#64 := by bv_arith
  have ha20 : a + 16#64 + BitVec.ofNat 64 4 = a + 20#64 := by bv_arith
  rw [ha4, ha8, ha16, ha20]

/-- Unified invariant for the cloned `pending_pre_key` at `+0x594`. -/
private def OptPendClone (A : RustAlloc) (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) : SepProp :=
  match orig with
  | none => ⌜pendCap' = noneCap⌝
  | some gp =>
    ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
      vecU8Buf A pendCap' pendPtr' gp.vec.bytes

/-- Unified invariant for the cloned `pending_kyber_pre_key` at `+0x594`. -/
private def OptKybClone (A : RustAlloc) (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) : SepProp :=
  match orig with
  | none => ⌜kybCap' = noneCap⌝
  | some gk =>
    ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
      vecU8Buf A kybCap' kybPtr' gk.vec.bytes

private theorem optTailVecAt_48_of_optPendClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) (w28 w2c : BitVec 32) (v08 : BitVec 64) (w24 : BitVec 32) :
    ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
      ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
      ((a + 40#64) ↦₃₂ w24) ∗ memRegion (a + 44#64) 4 ∗
      OptPendClone A orig pendCap' pendPtr') ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = orig.isSome⌝ ∗ optTailVecAt A 48 a pend' := by
  exact @SegCloneSteps.optTailVecAt_48_of_optPendClone A a orig pendCap' pendPtr' w28 w2c v08 w24

private theorem optTailVecAt_32_of_optKybClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) (w14 : BitVec 32) :
    ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
      ((a + 24#64) ↦₃₂ w14) ∗ memRegion (a + 28#64) 4 ∗
      OptKybClone A orig kybCap' kybPtr') ⊢
      ∃∗ kyb' : Option TailVecGhost, optTailVecAt A 32 a kyb' := by
  exact @SegCloneSteps.optTailVecAt_32_of_optKybClone A a orig kybCap' kybPtr' w14

/-- Values of the destination `SessionStructure` slots at `sp + 0xca0 .. sp + 0xdf8`. -/
private structure DstVals where
  w_ca0 : BitVec 64
  w_ca8 : BitVec 64
  w_cb0 : BitVec 64
  w_cb8 : BitVec 64
  w_cc0 : BitVec 64
  w_cc8 : BitVec 64
  w_cd0 : BitVec 64
  w_cd8 : BitVec 64
  w_ce0 : BitVec 64
  w_ce8 : BitVec 64
  w_cf0 : BitVec 64
  w_cf8 : BitVec 64
  w_d00 : BitVec 64
  w_d08 : BitVec 64
  w_d10 : BitVec 64
  w_d18 : BitVec 64
  w_d20 : BitVec 64
  w_d28 : BitVec 64
  w_d30 : BitVec 64
  q0 : BitVec 128
  q1 : BitVec 128
  q2 : BitVec 128
  q3 : BitVec 128
  q4 : BitVec 128
  q5 : BitVec 128
  w_d98 : BitVec 64
  w_da0 : BitVec 64
  w_da8 : BitVec 64
  w_db0 : BitVec 32
  w_db4 : BitVec 32
  w_db8 : BitVec 64
  w_dc0 : BitVec 32
  w_dc8 : BitVec 64
  w_dd0 : BitVec 64
  w_dd8 : BitVec 64
  w_de0 : BitVec 32
  w_de8 : BitVec 32
  w_dec : BitVec 32
  w_df0 : BitVec 32
  w_df4 : BitVec 32

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `sp + 0xca0`. -/
private def dstSlotsAt (sp : BitVec 64) (dv : DstVals) : SepProp :=
  ((sp + 0xca0#64) ↦₆₄ dv.w_ca0) ∗ ((sp + 0xca8#64) ↦₆₄ dv.w_ca8) ∗ ((sp + 0xcb0#64) ↦₆₄ dv.w_cb0) ∗
  ((sp + 0xcb8#64) ↦₆₄ dv.w_cb8) ∗ ((sp + 0xcc0#64) ↦₆₄ dv.w_cc0) ∗ ((sp + 0xcc8#64) ↦₆₄ dv.w_cc8) ∗
  ((sp + 0xcd0#64) ↦₆₄ dv.w_cd0) ∗ ((sp + 0xcd8#64) ↦₆₄ dv.w_cd8) ∗ ((sp + 0xce0#64) ↦₆₄ dv.w_ce0) ∗
  ((sp + 0xce8#64) ↦₆₄ dv.w_ce8) ∗ ((sp + 0xcf0#64) ↦₆₄ dv.w_cf0) ∗ ((sp + 0xcf8#64) ↦₆₄ dv.w_cf8) ∗
  ((sp + 0xd00#64) ↦₆₄ dv.w_d00) ∗ ((sp + 0xd08#64) ↦₆₄ dv.w_d08) ∗ ((sp + 0xd10#64) ↦₆₄ dv.w_d10) ∗
  ((sp + 0xd18#64) ↦₆₄ dv.w_d18) ∗ ((sp + 0xd20#64) ↦₆₄ dv.w_d20) ∗ ((sp + 0xd28#64) ↦₆₄ dv.w_d28) ∗
  ((sp + 0xd30#64) ↦₆₄ dv.w_d30) ∗
  chunks96_6QAt (sp + 0xd38#64) dv.q0 dv.q1 dv.q2 dv.q3 dv.q4 dv.q5 ∗
  ((sp + 0xd98#64) ↦₆₄ dv.w_d98) ∗ ((sp + 0xda0#64) ↦₆₄ dv.w_da0) ∗ ((sp + 0xda8#64) ↦₆₄ dv.w_da8) ∗
  ((sp + 0xdb0#64) ↦₃₂ dv.w_db0) ∗ ((sp + 0xdb4#64) ↦₃₂ dv.w_db4) ∗ ((sp + 0xdb8#64) ↦₆₄ dv.w_db8) ∗
  ((sp + 0xdc0#64) ↦₃₂ dv.w_dc0) ∗ memRegion (sp + 0xdc4#64) 4 ∗
  ((sp + 0xdc8#64) ↦₆₄ dv.w_dc8) ∗ ((sp + 0xdd0#64) ↦₆₄ dv.w_dd0) ∗ ((sp + 0xdd8#64) ↦₆₄ dv.w_dd8) ∗
  ((sp + 0xde0#64) ↦₃₂ dv.w_de0) ∗ memRegion (sp + 0xde4#64) 4 ∗
  ((sp + 0xde8#64) ↦₃₂ dv.w_de8) ∗ ((sp + 0xdec#64) ↦₃₂ dv.w_dec) ∗
  ((sp + 0xdf0#64) ↦₃₂ dv.w_df0) ∗ ((sp + 0xdf4#64) ↦₃₂ dv.w_df4)

private theorem memRegion_344_entails_dstSlotsAt (sp : BitVec 64) :
    memRegion (sp + 0xca0#64) 344 ⊢ ∃∗ dv : DstVals, dstSlotsAt sp dv := by
  rw [← sepConj_emp (memRegion (sp + 0xca0#64) 344)]
  refine elim_region8 (b' := sp + 0xca8#64) (rem := 336) rfl (by bv_arith) (by decide) fun w0 => ?_
  refine elim_region8 (b' := sp + 0xcb0#64) (rem := 328) rfl (by bv_arith) (by decide) fun w1 => ?_
  refine elim_region8 (b' := sp + 0xcb8#64) (rem := 320) rfl (by bv_arith) (by decide) fun w2 => ?_
  refine elim_region8 (b' := sp + 0xcc0#64) (rem := 312) rfl (by bv_arith) (by decide) fun w3 => ?_
  refine elim_region8 (b' := sp + 0xcc8#64) (rem := 304) rfl (by bv_arith) (by decide) fun w4 => ?_
  refine elim_region8 (b' := sp + 0xcd0#64) (rem := 296) rfl (by bv_arith) (by decide) fun w5 => ?_
  refine elim_region8 (b' := sp + 0xcd8#64) (rem := 288) rfl (by bv_arith) (by decide) fun w6 => ?_
  refine elim_region8 (b' := sp + 0xce0#64) (rem := 280) rfl (by bv_arith) (by decide) fun w7 => ?_
  refine elim_region8 (b' := sp + 0xce8#64) (rem := 272) rfl (by bv_arith) (by decide) fun w8 => ?_
  refine elim_region8 (b' := sp + 0xcf0#64) (rem := 264) rfl (by bv_arith) (by decide) fun w9 => ?_
  refine elim_region8 (b' := sp + 0xcf8#64) (rem := 256) rfl (by bv_arith) (by decide) fun w10 => ?_
  refine elim_region8 (b' := sp + 0xd00#64) (rem := 248) rfl (by bv_arith) (by decide) fun w11 => ?_
  refine elim_region8 (b' := sp + 0xd08#64) (rem := 240) rfl (by bv_arith) (by decide) fun w12 => ?_
  refine elim_region8 (b' := sp + 0xd10#64) (rem := 232) rfl (by bv_arith) (by decide) fun w13 => ?_
  refine elim_region8 (b' := sp + 0xd18#64) (rem := 224) rfl (by bv_arith) (by decide) fun w14 => ?_
  refine elim_region8 (b' := sp + 0xd20#64) (rem := 216) rfl (by bv_arith) (by decide) fun w15 => ?_
  refine elim_region8 (b' := sp + 0xd28#64) (rem := 208) rfl (by bv_arith) (by decide) fun w16 => ?_
  refine elim_region8 (b' := sp + 0xd30#64) (rem := 200) rfl (by bv_arith) (by decide) fun w17 => ?_
  refine elim_region8 (b' := sp + 0xd38#64) (rem := 192) rfl (by bv_arith) (by decide) fun w18 => ?_
  refine elim_region96_6Q (b' := sp + 0xd98#64) (rem := 96) rfl (by bv_arith) (by decide)
    fun q0 q1 q2 q3 q4 q5 => ?_
  refine elim_region8 (b' := sp + 0xda0#64) (rem := 88) rfl (by bv_arith) (by decide) fun w_d98 => ?_
  refine elim_region8 (b' := sp + 0xda8#64) (rem := 80) rfl (by bv_arith) (by decide) fun w_da0 => ?_
  refine elim_region8 (b' := sp + 0xdb0#64) (rem := 72) rfl (by bv_arith) (by decide) fun w_da8 => ?_
  refine elim_region4 (b' := sp + 0xdb4#64) (rem := 68) rfl (by bv_arith) (by decide) fun w_db0 => ?_
  refine elim_region4 (b' := sp + 0xdb8#64) (rem := 64) rfl (by bv_arith) (by decide) fun w_db4 => ?_
  refine elim_region8 (b' := sp + 0xdc0#64) (rem := 56) rfl (by bv_arith) (by decide) fun w_db8 => ?_
  refine elim_region4 (b' := sp + 0xdc4#64) (rem := 52) rfl (by bv_arith) (by decide) fun w_dc0 => ?_
  refine elim_region_skip (b' := sp + 0xdc8#64) (n := 4) (rem := 48) rfl (by bv_arith) (by decide) ?_
  refine elim_region8 (b' := sp + 0xdd0#64) (rem := 40) rfl (by bv_arith) (by decide) fun w_dc8 => ?_
  refine elim_region8 (b' := sp + 0xdd8#64) (rem := 32) rfl (by bv_arith) (by decide) fun w_dd0 => ?_
  refine elim_region8 (b' := sp + 0xde0#64) (rem := 24) rfl (by bv_arith) (by decide) fun w_dd8 => ?_
  refine elim_region4 (b' := sp + 0xde4#64) (rem := 20) rfl (by bv_arith) (by decide) fun w_de0 => ?_
  refine elim_region_skip (b' := sp + 0xde8#64) (n := 4) (rem := 16) rfl (by bv_arith) (by decide) ?_
  refine elim_region4 (b' := sp + 0xdec#64) (rem := 12) rfl (by bv_arith) (by decide) fun w_de8 => ?_
  refine elim_region4 (b' := sp + 0xdf0#64) (rem := 8) rfl (by bv_arith) (by decide) fun w_dec => ?_
  refine elim_region4 (b' := sp + 0xdf4#64) (rem := 4) rfl (by bv_arith) (by decide) fun w_df0 => ?_
  rw [memRegion_four (sp + 0xdf4#64), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w_df4
  refine Entails.sepExists_right
    ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      q0, q1, q2, q3, q4, q5, w_d98, w_da0, w_da8, w_db0, w_db4, w_db8, w_dc0,
      w_dc8, w_dd0, w_dd8, w_de0, w_de8, w_dec, w_df0, w_df4⟩ ?_
  dsimp only [dstSlotsAt]
  exact Entails.of_eq (by ac_rfl)

/-- All of `signalMessageAt` except the `message_version` byte at `+0x70`. -/
private def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    memRegion (a + 0x71#64) 7

private theorem signalMessageAt_eq_ver (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      (((a + 0x70#64) ↦₈ m.messageVersion) ∗ signalMessageRestAt A g a m) := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

/-! ## Field-cloning sub-segments (`+0x1a8 → +0x594`) -/

@[local simp, local arm64_norm]
private theorem int64_toBitVec_mk (u : UInt64) :
    ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl

@[local simp, local arm64_norm]
private theorem uint64_toBitVec_mk (v : BitVec 64) :
    ({ toBitVec := v } : UInt64).toBitVec = v := rfl

@[local simp, local arm64_norm]
private theorem uint64_toBitVec_ofNat (n : Nat) :
    (OfNat.ofNat n : UInt64).toBitVec = BitVec.ofNat 64 n := rfl

private theorem eq_nil_or_length_pos {α : Type} (l : List α) : l = [] ∨ 0 < l.length := by
  cases l with
  | nil => exact Or.inl rfl
  | cons _ _ => exact Or.inr (Nat.zero_lt_succ _)

/-- Entry frame initialization (`+0x1a8 → +0x1fc`): writes the closure environment at
`sp + 0x5b0..0x5d8`, the empty `errs` header at `sp + 0x5d8..0x5f0`, the spilled arguments at
`sp + 0x80..0xa0`, and checks `[sp + 0x138] ≠ -1` (`+0x1f8: b.eq` not taken). -/
private theorem seg_entry_to_0x1fc {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {v80 v88 v90 : BitVec 64} {v9c : BitVec 32}
    {v5b0 : BitVec 64} {v5bc : BitVec 8} {v5c0 v5c8 v5d0 v5d8 v5e0 v5e8 : BitVec 64}
    {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : x.G.localIk.cap < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (((s.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s.sp + 0x88#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x90#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
          ((s.sp + 0x5b0#64) ↦₆₄ x.remA) ∗
          ((s.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
          ((s.sp + 0x5c0#64) ↦₆₄ (s.sp + 0x5bc#64)) ∗
          ((s.sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x5d0#64) ↦₆₄ (s.sp + 0x5b0#64)) ∗
          errsAt A (s.sp + 0x5d8#64) [] ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
        ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
        ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
        ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
        ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.seg_entry_to_0x1fc img C A ctl S ext x R s0 s ret Q v80 v88 v90 v9c v5b0 v5bc v5c0 v5c8 v5d0 v5d8 v5e0 v5e8 F hpc hrun hsp h19 h27 h23 h24 htr hcap hnext

private theorem sepWPp_pure_2nd {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2) Q Qp) :
    SepWPp prog ret s (P1 ∗ ⌜φ⌝ ∗ P2) Q Qp := by
  rw [show P1 ∗ ⌜φ⌝ ∗ P2 = ⌜φ⌝ ∗ P1 ∗ P2 by ac_rfl]
  exact SepWPp.pure_elim h

private theorem sepWPp_pure_3rd {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact SepWPp.pure_elim h

private theorem entails_pure_2nd {P1 P2 P3 : SepProp} {φ : Prop}
    (hφ : φ) (heq : P1 = P2 ∗ P3) :
    P1 ⊢ P2 ∗ ⌜φ⌝ ∗ P3 := by
  rw [heq, show P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P2 ∗ P3 by ac_rfl]
  exact Entails.pure_right hφ (Entails.refl _)

/-- Clone `local_identity_key` (`+0x1fc → +0x504 / +0x238`) and load `w25 = session_version` and
`x22 = remote_identity_key.len`. -/
private theorem seg_localIk {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x504#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x238#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = localIk'.cap →
      s1.readReg64 .x21 = localIk'.ptr →
      s1.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.seg_localIk img C A ctl S ext hA x R s0 s ret Q F hpc hrun hsp htr hrem_lt hnext

/-- Clone `remote_identity_key` (`+0x504 / +0x238 → +0x268`) and load `x28 = 32` (`root_key.len`). -/
private theorem seg_remoteIk {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x504#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x238#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x268#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = remoteIk'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = remoteIk'.ptr →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
        ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.seg_remoteIk img C A ctl S ext hA x R s0 s ret Q F hpc hrun hsp hx22 htr hnext

/-- Clone `root_key` (`+0x268 → +0x290`, 32 bytes) and store the new pointer at `[sp + 0x48]`. -/
private theorem seg_rootKey {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v48 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x268#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x290#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.seg_rootKey img C A ctl S ext hA x R s0 s ret Q v48 F hpc hrun hsp hx28 htr hnext

private def optSenderChainSomeRest (A : RustAlloc) (a : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) : SepProp :=
  ⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
    sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
    Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
    sg.srk.bytes.length = 33⌝ ∗
    ((a + 8#64) ↦₆₄ sg.srk.ptr) ∗
    ((a + 16#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
    vecU8Buf A sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
    vecGhostAt A sg.priv (a + 0x18#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) sg.mkCap sg.mkPtr [] ∗
    optChainKeyAt A sg.ck (some sc.chainKey) (a + 0x48#64)

private theorem optSenderChainAt_some_eq_cap (A : RustAlloc) (a : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A a (some sg) (some sc) =
      ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
        (a ↦₆₄ sg.srk.cap) ∗ optSenderChainSomeRest A a sg sc := by
  dsimp only [optSenderChainAt, optSenderChainSomeRest]
  change (⌜PublicKey.deserialize sg.srk.bytes = .ok sc.ratchetKey.publicKey ∧
      sg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList ∧
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes ∧
      sg.srk.bytes.length = 33⌝ ∗
    vecU8At A a sg.srk.cap sg.srk.ptr sg.srk.bytes ∗
    vecGhostAt A sg.priv (a + 0x18#64) ∗
    vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) sg.mkCap sg.mkPtr [] ∗
    optChainKeyAt A sg.ck (some sc.chainKey) (a + 0x48#64)) = _
  rw [vecU8At_eq_header_sep_buf A a sg.srk.cap sg.srk.ptr sg.srk.bytes]
  conv => lhs; rw [vecU8Buf_pure_extract A sg.srk.cap sg.srk.ptr sg.srk.bytes]
  unfold vecHeader
  ac_rfl

private theorem chunks104W6QAt_entails_memRegion (a : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 ⊢ memRegion a 104 := by
  rw [chunks104W6QAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a (bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5)
  rwa [bytes104OfW6Q_length] at h

private theorem chunks104W6QAt_sp_0x5f0 (sp : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0x5f0#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0x5f0#64) ↦₆₄ w0) ∗
      (((sp + 0x5f0#64) + 0x8#64) ↦₁₂₈ q0) ∗
      (((sp + 0x5f0#64) + 0x18#64) ↦₁₂₈ q1) ∗
      (((sp + 0x5f0#64) + 0x28#64) ↦₁₂₈ q2) ∗
      (((sp + 0x5f0#64) + 0x38#64) ↦₁₂₈ q3) ∗
      (((sp + 0x5f0#64) + 0x48#64) ↦₁₂₈ q4) ∗
      (((sp + 0x5f0#64) + 0x58#64) ↦₁₂₈ q5) := rfl

private theorem chunks96_6QAt_sp_0xb40 (sp : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (sp + 0xb40#64) q0 q1 q2 q3 q4 q5 =
      ((sp + 0xb40#64) ↦₁₂₈ q0) ∗ ((sp + 0xb50#64) ↦₁₂₈ q1) ∗
      ((sp + 0xb60#64) ↦₁₂₈ q2) ∗ ((sp + 0xb70#64) ↦₁₂₈ q3) ∗
      ((sp + 0xb80#64) ↦₁₂₈ q4) ∗ ((sp + 0xb90#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  have h1 : sp + 0xb40#64 + 0x10#64 = sp + 0xb50#64 := by bv_arith
  have h2 : sp + 0xb40#64 + 0x20#64 = sp + 0xb60#64 := by bv_arith
  have h3 : sp + 0xb40#64 + 0x30#64 = sp + 0xb70#64 := by bv_arith
  have h4 : sp + 0xb40#64 + 0x40#64 = sp + 0xb80#64 := by bv_arith
  have h5 : sp + 0xb40#64 + 0x50#64 = sp + 0xb90#64 := by bv_arith
  rw [h1, h2, h3, h4, h5]

private theorem onPanic_of_callee_panic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {F R : SepProp} {s0 s_call sf : State}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  obtain ⟨⟨haf, hpre⟩, hm'⟩ := hm
  unfold allocFailedIn at haf
  rw [htr] at haf hpre
  rw [← sepConj_assoc] at hm'
  exact onPanic_of_allocFailed ⟨haf, hpre⟩ hm'

/-- Clone `sender_chain` (`+0x290 → +0x544 / +0x300`): spills `remoteIk'`, `localIk'`, `rootCap'`,
and `previous_counter`, clones `sender_chain` if `Some` (bouncing its 96 tail bytes through
`sp + 0xb40..+0xba0` and its cap word to `[sp + 0x40]`), or writes `noneCap` to `[sp + 0x40]` if
`None`, and branches on `x26 = receiver_chains.len`. -/
private theorem seg_senderChain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hsenderClone : SenderChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v40 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x290#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = localIk'.cap) (hx21 : s.readReg64 .x21 = localIk'.ptr)
    (hx22 : s.readReg64 .x22 = remoteIk'.cap) (hx26 : s.readReg64 .x26 = remoteIk'.ptr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x544#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      OptSenderChainInline sender' x.st.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          optSenderChainHeap A sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.seg_senderChain img C A ctl S ext hsenderClone x R s0 s ret Q localIk' remoteIk' v40 v58 v60 v68 v70 v78 v54 bq0 bq1 bq2 bq3 bq4 bq5 F hpc hrun hsp hx20 hx21 hx22 hx26 hx23 hx28 htr hrc_lt hnext

private theorem pointsTo128_eq_pointsTo64 (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) = ((a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v.extractLsb' 64 64)) := by
  unfold pointsTo128; rfl

private theorem cat128_extractLsb (v : BitVec 128) :
    v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by bv_kernel

private theorem chunks104_6QWAt_sp_0x5f0 (sp : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt (sp + 0x5f0#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp + 0x5f0#64) ↦₁₂₈ q0) ∗
      ((sp + 0x600#64) ↦₁₂₈ q1) ∗
      ((sp + 0x610#64) ↦₁₂₈ q2) ∗
      ((sp + 0x620#64) ↦₁₂₈ q3) ∗
      ((sp + 0x630#64) ↦₁₂₈ q4) ∗
      ((sp + 0x640#64) ↦₁₂₈ q5) ∗
      ((sp + 0x650#64) ↦₆₄ w6) := by
  unfold chunks104_6QWAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem chunks104_6QWAt_entails_memRegion (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ⊢ memRegion a 104 := by
  rw [chunks104_6QWAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a (bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)
  rwa [bytes104Of6QW_length] at h

private theorem memRegion_104_entails_chunks104_6QWAt (a : BitVec 64) :
    memRegion a 104 ⊢
      ∃∗ q0 : BitVec 128, ∃∗ q1 : BitVec 128, ∃∗ q2 : BitVec 128,
      ∃∗ q3 : BitVec 128, ∃∗ q4 : BitVec 128, ∃∗ q5 : BitVec 128,
      ∃∗ w6 : BitVec 64,
        chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 := by
  rw [← sepConj_emp (memRegion a 104)]
  refine elim_region96_6Q (b' := a + 0x60#64) (rem := 8) rfl rfl (by decide)
    fun q0 q1 q2 q3 q4 q5 => ?_
  rw [memRegion_eight (a + 0x60#64), sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w6
  refine Entails.sepExists_right q0 (Entails.sepExists_right q1
    (Entails.sepExists_right q2 (Entails.sepExists_right q3
      (Entails.sepExists_right q4 (Entails.sepExists_right q5
        (Entails.sepExists_right w6 ?_))))))
  unfold chunks96_6QAt chunks104_6QWAt
  exact Entails.of_eq (by ac_rfl)

private theorem segClone_bv_ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  have h : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 := BitVec.ofNat_add n 1
  rw [h]; bv_arith

private theorem segClone_bv_ofNat_mul_104 {n : Nat} :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (n * 104) := by
  simpa using (BitVec.ofNat_mul n 104).symm

private theorem segClone_bv_ofNat_mul_104_toNat {n : Nat} (hlt : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n * 104#64).toNat = n * 104 := by
  rw [segClone_bv_ofNat_mul_104, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem segClone_bv_ofNat_mul_104_beq_zero {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n * 104#64 == 0#64) = false := by
  rw [segClone_bv_ofNat_mul_104]
  exact beq_ofNat_zero_eq_false (by omega) (by omega)

private theorem segClone_off_add_succ_mul_104 (off : BitVec 64) (n : Nat) :
    off + BitVec.ofNat 64 (n + 1) * 104#64 =
      (off + 0x68#64) + BitVec.ofNat 64 n * 104#64 := by
  have h1 : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 := by
    simpa using BitVec.ofNat_add n 1
  rw [h1]
  bv_arith

/-- Copy the 104-byte cloned receiver chain from `sp + 0x5f0` to `dst = x23` (`+0x354 → +0x390 / +0x338`). -/
private theorem segClone_receiverChains_copy {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x354#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = off)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 rem)
    (hx22 : s.readReg64 .x22 = src + 0x68#64)
    (hx23 : s.readReg64 .x23 = dst)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : rem < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (if rem = 0 then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x390#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x338#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = off + 0x68#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = BitVec.ofNat 64 rem →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (chunks104_6QWAt (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (chunks104_6QWAt (s.sp + 0x5f0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_receiverChains_copy img C A ctl S ext x R s0 s ret Q rem src dst off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F hpc hrun hsp hx19 hx21 hx22 hx23 htr hrem_lt hnext

/-- Single iteration of the `receiver_chains` clone loop (`+0x338 → +0x390 / +0x338`). -/
private theorem segClone_receiverChains_iter {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hchainClone : ChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x338#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = src)
    (hx19 : s.readReg64 .x19 = off)
    (hx20 : s.readReg64 .x20 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (rem + 1))
    (hx28 : s.readReg64 .x28 = dst_base)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      s1.pc = (if rem = 0 then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x390#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x338#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = off + 0x68#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = BitVec.ofNat 64 rem →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = dst_base →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_receiverChains_iter img C A ctl S ext hchainClone x R s0 s ret Q g rc rem src dst_base off F hpc hrun hsp hx1 hx19 hx20 hx21 hx28 htr hmul_lt hnext

/-- Induction over `rcs_tl` for the `receiver_chains` clone loop (`+0x338 → +0x390`). -/
private theorem segClone_receiverChains_loop {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hchainClone : ChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x338#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x1 = src →
      s.readReg64 .x19 = off →
      s.readReg64 .x20 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x21 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x28 = dst_base →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x390#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        s1.spAligned = true →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x28 = dst_base →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_receiverChains_loop img C A ctl S ext hchainClone x R s0 ret Q dst_base rcs_tl

private def segClone_vecBufRest {α : Type} (A : RustAlloc) (stride align : Nat)
    (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr (cap.toNat * stride) align ∗
     memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))

private theorem segClone_vecBuf_expose_arrayAt {α : Type} (A : RustAlloc) {stride : Nat}
    (align : Nat) (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α)
    (R_tail : SepProp) :
    vecBuf A stride align elem cap ptr xs ∗ R_tail ⊢
      ⌜xs.length * stride < 2 ^ 63⌝ ∗
      arrayAt elem stride ptr xs ∗
      segClone_vecBufRest A stride align cap ptr xs ∗ R_tail := by
  have h :
      vecBuf A stride align elem cap ptr xs ⊢
        ⌜xs.length * stride < 2 ^ 63⌝ ∗
        arrayAt elem stride ptr xs ∗
        segClone_vecBufRest A stride align cap ptr xs := by
    unfold vecBuf segClone_vecBufRest
    apply Entails.pure_left
    rintro ⟨hlen, hlt, hptr⟩
    have hxs_lt : xs.length * stride < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right stride hlen) hlt
    apply Entails.pure_right hxs_lt
    rw [sepConj_pure_left_comm]
    apply Entails.pure_right ⟨hlen, hlt, hptr⟩
    by_cases hcap : cap = 0
    · subst hcap
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst hnil
      simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [hcap, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
  simpa only [sepConj_assoc] using sepConj_mono_left (Q := R_tail) h

private theorem segClone_vecBuf_reassemble_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
    (elem : α → BitVec 64 → SepProp) (cap ptr : BitVec 64) (xs : List α) :
    arrayAt elem stride ptr xs ∗ segClone_vecBufRest A stride align cap ptr xs ⊢
      vecBuf A stride align elem cap ptr xs := by
  unfold vecBuf segClone_vecBufRest
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hlen, hlt, hptr⟩
  apply Entails.pure_right ⟨hlen, hlt, hptr⟩
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hnil
    simp only [↓reduceIte, arrayAt_nil, emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

private theorem segClone_vecBuf_chain_nil_eq (A : RustAlloc) :
    vecBuf A 104 8 (chainAt A) 0#64 8#64 [] = emp := by
  unfold vecBuf
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.pure_left; intro _
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _
  · apply Entails.pure_right ⟨by decide, by decide, by decide⟩
    have h0 : (0#64 : BitVec 64) = 0 := rfl
    simp only [h0, ↓reduceIte]
    exact Entails.refl _

private theorem segClone_vecBuf_chain_of_arrayAt (A : RustAlloc) (ptr' : BitVec 64)
    (xs : List (ChainGhost × ReceiverChain))
    (hpos : 0 < xs.length) (hlt : xs.length * 104 < 2 ^ 63) (hptr' : ptr' ≠ 0#64) :
    (A.live ptr' (xs.length * 104) 8 ∗ arrayAt (chainAt A) 104 ptr' xs) ⊢
      vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 xs.length) ptr' xs := by
  unfold vecBuf
  have htoNat : (BitVec.ofNat 64 xs.length).toNat = xs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne0 : BitVec.ofNat 64 xs.length ≠ 0 := by
    intro h0
    have ht := congrArg BitVec.toNat h0
    rw [htoNat] at ht; change xs.length = 0 at ht; omega
  have hptr_ne : ptr' ≠ 0 := hptr'
  apply Entails.pure_right ⟨by rw [htoNat], by rw [htoNat]; exact hlt, hptr_ne⟩
  simp only [hne0, ↓reduceIte, htoNat, Nat.sub_self, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp]
  exact Entails.refl _

/-- Clones `receiver_chains` (`+0x544 / +0x300 → +0x548 / +0x390`) into `x28 = chainsPtr'`. -/
private theorem segClone_receiverChains {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hchainClone : ChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.st.receiverChains = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x544#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x300#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.pc = (if x.st.receiverChains = [] then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x548#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x390#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x28 = chainsPtr' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_receiverChains img C A ctl S ext hA hchainClone x R s0 s ret Q F hpc hrun hsp hx26 htr hchains_len hnext

/-- Clones `pending_pre_key` (`+0x548 / +0x390 → +0x558 / +0x1904 / +0x3e8`). -/
private theorem segClone_pendingPreKey {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x548#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x390#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x558#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1904#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x3e8#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_pendingPreKey img C A ctl S ext hA x R s0 s ret Q v08 v18 v24 v28 v2c F hpc hrun hsp htr hnext

private theorem segClone_pendingKyber_3f8_pos {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gk : TailVecGhost} {kw0 kw1 : BitVec 32}
    {v00 : BitVec 64} {v14 : BitVec 32} {F : SepProp}
    (htail : gk.tail.length = 32 - 24)
    (htail_pts : ∀ a : BitVec 64,
      (a ↦ₛ gk.tail) = ((a ↦₃₂ kw0) ∗ ((a + 4#64) ↦₃₂ kw1)))
    (hpos : 0 < gk.vec.bytes.length)
    (hlen_le : gk.vec.bytes.length ≤ gk.vec.cap.toNat)
    (hcap_lt : gk.vec.cap.toNat < 2 ^ 63)
    (hptr : gk.vec.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x3f8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x56c#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1920#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          (⌜gk.tail.length = 32 - 24⌝ ∗
            vecGhostAt A gk.vec (s.sp + 0x260#64) ∗
            ((s.sp + 0x260#64 + BitVec.ofNat 64 24) ↦ₛ gk.tail)) ∗
          (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((s.sp + 0x260#64) ↦₆₄ gk.vec.cap) ∗
        ((s.sp + 0x268#64) ↦₆₄ gk.vec.ptr) ∗
        ((s.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗
        (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
        A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
        memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
          (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
        ((s.sp + 0x278#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x27c#64) ↦₃₂ kw1) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_pendingKyber_3f8_pos img C A ctl S ext hA x R s0 s ret Q gk kw0 kw1 v00 v14 F htail htail_pts hpos hlen_le hcap_lt hptr hpc hrun hsp htr hnext

/-- Stores `[sp + 0x3c] = w25` (`session_version`) and clones `pending_kyber_pre_key` (`+0x558 / +0x1904 / +0x3e8 → +0x56c / +0x1920 / +0x430`). -/
private theorem segClone_pendingKyber {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 : BitVec 64} {v14 v3c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x558#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1904#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x3e8#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x56c#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1920#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x430#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_pendingKyber img C A ctl S ext hA x R s0 s ret Q v00 v14 v3c F hpc hrun hsp htr hnext

private theorem segClone_aliceBaseKey_444_pos {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (halice : 0 < x.G.alice.bytes.length)
    (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63)
    (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        (s.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗
        (s.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
        (s.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗
        (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
        A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
          (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_aliceBaseKey_444_pos img C A ctl S ext hA x R s0 s ret Q F halice hlen_le hcap_lt hptr hpc hrun hsp hx25 htr hnext

/-- Clones `alice_base_key` (`+0x56c / +0x1920 / +0x430 → +0x584 / +0x46c`) and loads registration IDs. -/
private theorem segClone_aliceBaseKey {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x56c#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1920#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x430#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x584#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_aliceBaseKey img C A ctl S ext hA x R s0 s ret Q v30 w288 w28c F hpc hrun hsp htr hnext

private theorem segClone_pqRatchet_478_pos {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (hpq : 0 < x.st.pqRatchetState.length)
    (hlen_le : x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63)
    (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x478#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        (s.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗
        (s.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
        (s.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗
        (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length)
          (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_pqRatchet_478_pos img C A ctl S ext hA x R s0 s ret Q F hpq hlen_le hcap_lt hptr hpc hrun hsp hx20 htr hnext

/-- Clones `pq_ratchet_state` (`+0x584 / +0x46c → +0x594`) and restores `x24 = sp + 0xca0`. -/
private theorem segClone_pqRatchet {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {F : SepProp}
    (hpc : s.pc = (if x.G.alice.bytes = [] then
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x584#64
                   else
                     (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x46c#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_pqRatchet img C A ctl S ext hA x R s0 s ret Q F hpc hrun hsp hx24 htr hnext

/-! ## Destination `SessionStructure` reassembly and version check (`+0x594 → +0x69c / +0x7e4`) -/

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `sp + 0xca0` after
the stores in `+0x594..+0x694`. -/
private def segClone_dstSlotsWrittenAt (sp : BitVec 64)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w28 w2c : BitVec 32) (v08 : BitVec 64) (w24 : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (w14 : BitVec 32)
    (sessionVersion previousCounter w288 w28c : BitVec 32) : SepProp :=
  ((sp + 0xca0#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xca8#64) ↦₆₄ localIk'.ptr) ∗ ((sp + 0xcb0#64) ↦₆₄ localIk'.cap) ∗
  ((sp + 0xcb8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xcc0#64) ↦₆₄ remoteIk'.ptr) ∗ ((sp + 0xcc8#64) ↦₆₄ remoteIk'.cap) ∗
  ((sp + 0xcd0#64) ↦₆₄ 32#64) ∗ ((sp + 0xcd8#64) ↦₆₄ rootPtr') ∗ ((sp + 0xce0#64) ↦₆₄ 32#64) ∗
  ((sp + 0xce8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xcf0#64) ↦₆₄ chainsPtr') ∗ ((sp + 0xcf8#64) ↦₆₄ chainsCap') ∗
  ((sp + 0xd00#64) ↦₆₄ alice'.cap) ∗ ((sp + 0xd08#64) ↦₆₄ alice'.ptr) ∗ ((sp + 0xd10#64) ↦₆₄ alice'.cap) ∗
  ((sp + 0xd18#64) ↦₆₄ pqCap') ∗ ((sp + 0xd20#64) ↦₆₄ pqPtr') ∗ ((sp + 0xd28#64) ↦₆₄ pqCap') ∗
  ((sp + 0xd30#64) ↦₆₄ scCap') ∗
  chunks96_6QAt (sp + 0xd38#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
  ((sp + 0xd98#64) ↦₆₄ pendCap') ∗ ((sp + 0xda0#64) ↦₆₄ pendPtr') ∗ ((sp + 0xda8#64) ↦₆₄ pendCap') ∗
  ((sp + 0xdb0#64) ↦₃₂ w28) ∗ ((sp + 0xdb4#64) ↦₃₂ w2c) ∗ ((sp + 0xdb8#64) ↦₆₄ v08) ∗
  ((sp + 0xdc0#64) ↦₃₂ w24) ∗ memRegion (sp + 0xdc4#64) 4 ∗
  ((sp + 0xdc8#64) ↦₆₄ kybCap') ∗ ((sp + 0xdd0#64) ↦₆₄ kybPtr') ∗ ((sp + 0xdd8#64) ↦₆₄ kybCap') ∗
  ((sp + 0xde0#64) ↦₃₂ w14) ∗ memRegion (sp + 0xde4#64) 4 ∗
  ((sp + 0xde8#64) ↦₃₂ sessionVersion) ∗ ((sp + 0xdec#64) ↦₃₂ previousCounter) ∗
  ((sp + 0xdf0#64) ↦₃₂ w288) ∗ ((sp + 0xdf4#64) ↦₃₂ w28c)

private theorem segClone_dstSlotsWrittenAt_entails_sessionStateAt
    (A : RustAlloc) (sp : BitVec 64) (x : RecordDecryptGhost)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
    (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64)
    (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w28 w2c : BitVec 32) (v08 : BitVec 64) (w24 : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (w14 : BitVec 32)
    (w288 w28c : BitVec 32)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (h_rem_deser : match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_pend_some : x.G.pending.isSome = x.st.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c))
    (hloc_bytes : localIk'.bytes = x.G.localIk.bytes)
    (hloc_cap : localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length)
    (hrem_bytes : remoteIk'.bytes = x.G.remoteIk.bytes)
    (hrem_cap : remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hchains_len : chains'.length = x.st.receiverChains.length)
    (hchains_cap : chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length)
    (halice_bytes : alice'.bytes = x.G.alice.bytes)
    (halice_cap : alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hpq_cap : pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (hsc_inl : OptSenderChainInline sender' x.st.senderChain
      (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5)) :
    (segClone_dstSlotsWrittenAt sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
        pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
        kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
      vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
      vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
      vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
      vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
      vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
      vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
      optSenderChainHeap A sender' x.st.senderChain ∗
      OptPendClone A x.G.pending pendCap' pendPtr' ∗
      OptKybClone A x.G.kyber kybCap' kybPtr') ⊢
      ∃∗ G₁ : SessionGhost,
        ⌜CloneRel x.G G₁⌝ ∗ sessionStateAt A (sp + 0xca0#64) G₁ x.st := by
  exact @SegCloneSteps.segClone_dstSlotsWrittenAt_entails_sessionStateAt A sp x localIk' remoteIk' rootPtr' chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24 kybCap' kybPtr' w14 w288 w28c h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts hloc_bytes hloc_cap hrem_bytes hrem_cap hchains_len hchains_cap halice_bytes halice_cap hpq_cap hsc_inl

private theorem segClone_chunks96_6QAt_sp_0xd38 (sp : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (sp + 0xd38#64) q0 q1 q2 q3 q4 q5 =
      ((sp + 0xd38#64) ↦₁₂₈ q0) ∗ ((sp + 0xd48#64) ↦₁₂₈ q1) ∗
      ((sp + 0xd58#64) ↦₁₂₈ q2) ∗ ((sp + 0xd68#64) ↦₁₂₈ q3) ∗
      ((sp + 0xd78#64) ↦₁₂₈ q4) ∗ ((sp + 0xd88#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private def segClone_dstSlotsMidAt (sp : BitVec 64) (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendPtr' : BitVec 64) : SepProp :=
  ((sp + 0xca0#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xca8#64) ↦₆₄ localIk'.ptr) ∗ ((sp + 0xcb0#64) ↦₆₄ localIk'.cap) ∗
  ((sp + 0xcb8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xcc0#64) ↦₆₄ remoteIk'.ptr) ∗ ((sp + 0xcc8#64) ↦₆₄ remoteIk'.cap) ∗
  ((sp + 0xcd0#64) ↦₆₄ 32#64) ∗ ((sp + 0xcd8#64) ↦₆₄ rootPtr') ∗ ((sp + 0xce0#64) ↦₆₄ 32#64) ∗
  ((sp + 0xce8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xcf0#64) ↦₆₄ chainsPtr') ∗ ((sp + 0xcf8#64) ↦₆₄ chainsCap') ∗
  ((sp + 0xd00#64) ↦₆₄ dv.w_d00) ∗ ((sp + 0xd08#64) ↦₆₄ dv.w_d08) ∗ ((sp + 0xd10#64) ↦₆₄ dv.w_d10) ∗
  ((sp + 0xd18#64) ↦₆₄ dv.w_d18) ∗ ((sp + 0xd20#64) ↦₆₄ dv.w_d20) ∗ ((sp + 0xd28#64) ↦₆₄ dv.w_d28) ∗
  ((sp + 0xd30#64) ↦₆₄ scCap') ∗
  chunks96_6QAt (sp + 0xd38#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
  ((sp + 0xd98#64) ↦₆₄ dv.w_d98) ∗ ((sp + 0xda0#64) ↦₆₄ pendPtr') ∗ ((sp + 0xda8#64) ↦₆₄ dv.w_da8) ∗
  ((sp + 0xdb0#64) ↦₃₂ dv.w_db0) ∗ ((sp + 0xdb4#64) ↦₃₂ dv.w_db4) ∗ ((sp + 0xdb8#64) ↦₆₄ dv.w_db8) ∗
  ((sp + 0xdc0#64) ↦₃₂ dv.w_dc0) ∗ memRegion (sp + 0xdc4#64) 4 ∗
  ((sp + 0xdc8#64) ↦₆₄ dv.w_dc8) ∗ ((sp + 0xdd0#64) ↦₆₄ dv.w_dd0) ∗ ((sp + 0xdd8#64) ↦₆₄ dv.w_dd8) ∗
  ((sp + 0xde0#64) ↦₃₂ dv.w_de0) ∗ memRegion (sp + 0xde4#64) 4 ∗
  ((sp + 0xde8#64) ↦₃₂ dv.w_de8) ∗ ((sp + 0xdec#64) ↦₃₂ dv.w_dec) ∗
  ((sp + 0xdf0#64) ↦₃₂ dv.w_df0) ∗ ((sp + 0xdf4#64) ↦₃₂ dv.w_df4)

/-- First half of destination slot assembly (`+0x594 → +0x620`, 35 instructions). -/
private theorem segClone_assemble_1 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (w14 : BitVec 32) (pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (sessionVersion previousCounter : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x620#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x8 = w2c.setWidth 64 →
      s1.readReg64 .x9 = w28.setWidth 64 →
      s1.readReg64 .x10 = previousCounter.setWidth 64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
          scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
            scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp v00 v08 w14 pendPtr' w24 w28 w2c chainsCap' sessionVersion
          scCap' rootPtr' previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_assemble_1 img C A ctl S ext x R s0 s ret Q ⟨dv.1, dv.2, dv.3, dv.4, dv.5, dv.6, dv.7, dv.8, dv.9, dv.10, dv.11, dv.12, dv.13, dv.14, dv.15, dv.16, dv.17, dv.18, dv.19, dv.20, dv.21, dv.22, dv.23, dv.24, dv.25, dv.26, dv.27, dv.28, dv.29, dv.30, dv.31, dv.32, dv.33, dv.34, dv.35, dv.36, dv.37, dv.38, dv.39, dv.40⟩ localIk' remoteIk' rootPtr' chainsCap' chainsPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 v00 v08 w14 pendPtr' w24 w28 w2c sessionVersion previousCounter F hpc hrun hsp hx24 hx28 htr hnext

private theorem segClone_version_cond_iff (sv : BitVec 32) (mv : BitVec 8) :
    ((if sv = 0 then 2#64 else BitVec.truncate 64 sv) = BitVec.zeroExtend 64 mv) ↔
      (if sv = 0 then 2 else sv) = mv.setWidth 32 := by
  bv_kernel

/-- Second half of destination slot assembly and version check (`+0x620 → +0x69c / +0x7e4`, 31 instructions). -/
private theorem segClone_assemble_2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (w288 w28c : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x620#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = w2c.setWidth 64)
    (hx9 : s.readReg64 .x9 = w28.setWidth 64)
    (hx10 : s.readReg64 .x10 = x.st.previousCounter.setWidth 64)
    (hx19 : s.readReg64 .x19 = kybCap')
    (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64)
    (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64)
    (_hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap)
    (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x69c#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x7e4#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (segClone_dstSlotsMidAt s.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
        scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  exact @SegCloneSteps.segClone_assemble_2 img C A ctl S ext x R s0 s ret Q ⟨dv.1, dv.2, dv.3, dv.4, dv.5, dv.6, dv.7, dv.8, dv.9, dv.10, dv.11, dv.12, dv.13, dv.14, dv.15, dv.16, dv.17, dv.18, dv.19, dv.20, dv.21, dv.22, dv.23, dv.24, dv.25, dv.26, dv.27, dv.28, dv.29, dv.30, dv.31, dv.32, dv.33, dv.34, dv.35, dv.36, dv.37, dv.38, dv.39, dv.40⟩ localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice' pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr' w24 w28 w2c w288 w28c F hpc hrun hsp hx8 hx9 hx10 hx19 hx20 hx21 hx22 hx23 _hx24 hx25 hx26 hx27 htr hnext

/-! ## Top-level composition (`segClone_ok`) -/

private theorem segClone_sessionStateAt_0x138_eq (A : RustAlloc) (sp : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (sp + 0x138#64) G st =
      ⌜PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
        (match st.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
        G.chains.length = st.receiverChains.length ∧
        G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
        G.localIk.bytes.length = 33 ∧
        (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
      vecGhostAt A G.localIk (sp + 0x138#64) ∗
      vecGhostAt A G.remoteIk (sp + 0x150#64) ∗
      vecU8At A (sp + 0x168#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (sp + 0x180#64) G.chainsCap G.chainsPtr
        (G.chains.zip st.receiverChains) ∗
      vecGhostAt A G.alice (sp + 0x198#64) ∗
      vecU8At A (sp + 0x1b0#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
      optSenderChainAt A (sp + 0x1c8#64) G.sender st.senderChain ∗
      optTailVecAt A 48 (sp + 0x230#64) G.pending ∗
      optTailVecAt A 32 (sp + 0x260#64) G.kyber ∗
      ((sp + 0x280#64) ↦₃₂ st.sessionVersion) ∗
      ((sp + 0x284#64) ↦₃₂ st.previousCounter) ∗
      ((sp + 0x288#64) ↦ₛ G.regIds) := by
  unfold sessionStateAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

private theorem segClone_memRegion_0xa0_eq (sp : BitVec 64) :
    memRegion sp 0xa0 = memRegion sp 0x80 ∗ memRegion (sp + 0x80#64) 0x20 :=
  memRegion_split' (b := sp) (b' := sp + 0x80#64) (n := 0x80) (k := 0x20) rfl rfl (by decide)

private theorem segClone_memRegion_0x4b0_0x950_eq (sp : BitVec 64) :
    memRegion (sp + 0x4b0#64) 0x950 =
      memRegion (sp + 0x4b0#64) 48 ∗
      memRegion (sp + 0x4e0#64) 0xd0 ∗
      memRegion (sp + 0x5b0#64) 0x40 ∗
      memRegion (sp + 0x5f0#64) 0x6b0 ∗
      memRegion (sp + 0xca0#64) 344 ∗
      memRegion (sp + 0xdf8#64) 8 := by
  rw [memRegion_split' (b := sp + 0x4b0#64) (b' := sp + 0x4e0#64) (n := 48) (k := 2336) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x4e0#64) (b' := sp + 0x5b0#64) (n := 0xd0) (k := 2128) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x5b0#64) (b' := sp + 0x5f0#64) (n := 0x40) (k := 2064) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x5f0#64) (b' := sp + 0xca0#64) (n := 0x6b0) (k := 352) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xca0#64) (b' := sp + 0xdf8#64) (n := 344) (k := 8) rfl (by bv_arith) (by decide)]

private theorem segClone_vecGhostAt_0x138_eq (A : RustAlloc) (g : VecGhost) (sp : BitVec 64) :
    vecGhostAt A g (sp + 0x138#64) =
      ((sp + 0x138#64) ↦₆₄ g.cap) ∗ ((sp + 0x140#64) ↦₆₄ g.ptr) ∗
      ((sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have h1 : sp + 0x138#64 + 8#64 = sp + 0x140#64 := by bv_arith
  have h2 : sp + 0x138#64 + 16#64 = sp + 0x148#64 := by bv_arith
  rw [h1, h2]
  ac_rfl

private theorem segClone_vecGhostAt_0x150_eq (A : RustAlloc) (g : VecGhost) (sp : BitVec 64) :
    vecGhostAt A g (sp + 0x150#64) =
      ((sp + 0x150#64) ↦₆₄ g.cap) ∗ ((sp + 0x158#64) ↦₆₄ g.ptr) ∗
      ((sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have h1 : sp + 0x150#64 + 8#64 = sp + 0x158#64 := by bv_arith
  have h2 : sp + 0x150#64 + 16#64 = sp + 0x160#64 := by bv_arith
  rw [h1, h2]
  ac_rfl

private theorem segClone_vecU8At_0x168_root_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
    (rk : BitVec 256) :
    vecU8At A (sp + 0x168#64) cap ptr (keyToBytes32 rk) =
      ((sp + 0x168#64) ↦₆₄ cap) ∗ ((sp + 0x170#64) ↦₆₄ ptr) ∗
      ((sp + 0x178#64) ↦₆₄ 32#64) ∗
      vecU8Buf A cap ptr (keyToBytes32 rk) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have h1 : sp + 0x168#64 + 8#64 = sp + 0x170#64 := by bv_arith
  have h2 : sp + 0x168#64 + 16#64 = sp + 0x178#64 := by bv_arith
  have h3 : BitVec.ofNat 64 (keyToBytes32 rk).length = 32#64 := by simp [keyToBytes32]
  rw [h1, h2, h3]
  ac_rfl

private theorem segClone_vecAt_0x180_chains_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
    (gs : List ChainGhost) (rcs : List ReceiverChain)
    (hlen : gs.length = rcs.length) :
    vecAt A 104 8 (chainAt A) (sp + 0x180#64) cap ptr (gs.zip rcs) =
      ((sp + 0x180#64) ↦₆₄ cap) ∗ ((sp + 0x188#64) ↦₆₄ ptr) ∗
      ((sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 rcs.length) ∗
      vecBuf A 104 8 (chainAt A) cap ptr (gs.zip rcs) := by
  unfold vecAt vecHeader
  have h1 : sp + 0x180#64 + 8#64 = sp + 0x188#64 := by bv_arith
  have h2 : sp + 0x180#64 + 16#64 = sp + 0x190#64 := by bv_arith
  have h3 : (gs.zip rcs).length = rcs.length := by simp [hlen]
  rw [h1, h2, h3]
  ac_rfl

private def segClone_fixedRest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x4b0#64) 48 ∗ memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  errsAt A (sp + 0x5d8#64) [] ∗
  memRegion (sp + 0x658#64) 0x4e8 ∗ memRegion (sp + 0xba0#64) 0x100 ∗
  memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  tapeAt ctl x.cur x.rest ∗ logOff img ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack)

private theorem segClone_fixedRest_reassemble (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (sp : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (v00 v08 : BitVec 64) (v14 : BitVec 32) (v18 : BitVec 64)
    (v24 v28 v2c : BitVec 32) (v30 : BitVec 64) (v3c : BitVec 32)
    (v40 v48 : BitVec 64) (v54 : BitVec 32) (v58 v60 v68 v70 v78 : BitVec 64) :
    (spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78 ∗
      chunks96_6QAt (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
      memRegion (sp + 0x5f0#64) 104 ∗
      ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
      stackAt sp allocHookStack ∗ A.pool ∗
      segClone_fixedRest A ctl img x sp) ⊢
      (recFrame A img x sp ∗ errsAt A (sp + 0x5d8#64) [] ∗
        memRegion (sp + 0x4b0#64) 48 ∗ tapeAt ctl x.cur x.rest) := by
  refine Entails.trans
    (sepConj_mono
      (spillSlotsAt_entails_memRegion_0x80 sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78)
      (sepConj_mono_left (chunks96_6QAt_entails_memRegion (sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5))) ?_
  unfold segClone_fixedRest recFrame
  rw [memRegion_0x5f0_0x6b0_eq sp, stackAt_root_eq_chainClone sp, stackAt_chainClone_eq_alloc sp]
  exact Entails.of_eq (by ac_rfl)

private theorem segClone_srcSessionState_reassemble (A : RustAlloc) (sp : BitVec 64)
    (x : RecordDecryptGhost) (w288 w28c : BitVec 32)
    (h_loc_deser : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (h_rem_deser : match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (h_chains_len : x.G.chains.length = x.st.receiverChains.length)
    (h_pend_some : x.G.pending.isSome = x.st.pendingPreKey)
    (h_reg_len : x.G.regIds.length = 8)
    (h_loc_len : x.G.localIk.bytes.length = 33)
    (h_rem_len : x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)
    (h_reg_pts : ∀ a : BitVec 64, (a ↦ₛ x.G.regIds) = (a ↦₃₂ w288) ∗ ((a + 4#64) ↦₃₂ w28c)) :
    (vecGhostAt A x.G.localIk (sp + 0x138#64) ∗
      vecGhostAt A x.G.remoteIk (sp + 0x150#64) ∗
      vecU8At A (sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
      vecAt A 104 8 (chainAt A) (sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
        (x.G.chains.zip x.st.receiverChains) ∗
      vecGhostAt A x.G.alice (sp + 0x198#64) ∗
      vecU8At A (sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
      optSenderChainAt A (sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
      optTailVecAt A 48 (sp + 0x230#64) x.G.pending ∗
      optTailVecAt A 32 (sp + 0x260#64) x.G.kyber ∗
      ((sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
      ((sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
      ((sp + 0x288#64) ↦₃₂ w288) ∗
      ((sp + 0x28c#64) ↦₃₂ w28c)) ⊢
      sessionStateAt A (sp + 0x138#64) x.G x.st := by
  rw [segClone_sessionStateAt_0x138_eq]
  apply Entails.pure_right ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  have h28c : sp + 0x288#64 + 4#64 = sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (sp + 0x288#64), h28c]
  exact Entails.of_eq (by ac_rfl)

private theorem segClone_entry_combined {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (sv : SpillVals) (dv : DstVals)
      (bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          dstSlotsAt s.sp dv ∗
          spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
            sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
          chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
          stackAt s.sp allocHookStack ∗
          segClone_fixedRest A ctl img x s.sp ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (memRegion s.sp 0xa0 ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        memRegion (s.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_memRegion_0xa0_eq s.sp, segClone_memRegion_0x4b0_0x950_eq s.sp,
      memRegion_0x5f0_0x6b0_eq s.sp, signalMessageAt_eq_ver A x.msgG x.msgA x.msg,
      stackAt_root_eq_chainClone s.sp, stackAt_chainClone_eq_alloc s.sp,
      segClone_vecGhostAt_0x138_eq A x.G.localIk s.sp,
      vecU8Buf_pure_extract A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes]
  simp only [sepConj_assoc]
  refine SepWPp.weaken_pre
    (sepConj_mono (memRegion_0x80_entails_spillSlotsAt s.sp)
      (sepConj_mono_left (memRegion_0x80_0x20_entails s.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v80 => SepWPp.exists_elim fun v88 =>
    SepWPp.exists_elim fun v90 => SepWPp.exists_elim fun v9c =>
    SepWPp.exists_elim fun sv => ?_
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
              x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
            memRegion (s.sp + 0x5b0#64) 0x40 ∗
            memRegion (s.sp + 0xca0#64) 344 ∗
            memRegion (s.sp + 0xb40#64) 96 ∗
            (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
              ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
              ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
              ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
              ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
              ((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageRestAt A x.msgG x.msgA x.msg ∗
              tapeAt ctl x.cur x.rest ∗ logOff img ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, _⟩ => ?_
  refine SepWPp.weaken_pre
    (sepConj_mono (memRegion_0x5b0_0x40_entails s.sp)
      (sepConj_mono (memRegion_344_entails_dstSlotsAt s.sp)
        (sepConj_mono_left (Entails.of_eq (memRegion_96_eq_exists_chunks96_6QAt (s.sp + 0xb40#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun bq0 => SepWPp.exists_elim fun bq1 =>
    SepWPp.exists_elim fun bq2 => SepWPp.exists_elim fun bq3 =>
    SepWPp.exists_elim fun bq4 => SepWPp.exists_elim fun bq5 =>
    SepWPp.exists_elim fun dv =>
    SepWPp.exists_elim fun v5b0 => SepWPp.exists_elim fun v5bc =>
    SepWPp.exists_elim fun v5c0 => SepWPp.exists_elim fun v5c8 =>
    SepWPp.exists_elim fun v5d0 => SepWPp.exists_elim fun v5d8 =>
    SepWPp.exists_elim fun v5e0 => SepWPp.exists_elim fun v5e8 => ?_
  refine SepWPp.weaken_pre
    (P' := ((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
            ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
            ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
            ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
            ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
            ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
            ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
            ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            (((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              dstSlotsAt s.sp dv ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x5b8#64) 4 ∗ memRegion (s.sp + 0x5bd#64) 3 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageRestAt A x.msgG x.msgA x.msg ∗
              tapeAt ctl x.cur x.rest ∗ logOff img ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine seg_entry_to_0x1fc hpc hrun hsp h19 h27 h23 h24 htr hcap_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  refine SepWPp.weaken_pre ?_
    (hnext s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1)
  unfold segClone_fixedRest
  rw [segClone_vecGhostAt_0x138_eq A x.G.localIk s.sp, signalMessageAt_eq_ver A x.msgG x.msgA x.msg]
  exact Entails.of_eq (by ac_rfl)

private theorem segClone_fields_1_to_4 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hsenderClone : SenderChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v40 v48 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x544#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.st.senderChain
        (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          optSenderChainHeap A sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
        vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s.sp,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      segClone_vecU8At_0x168_root_eq A s.sp x.G.root.cap x.G.root.ptr x.st.rootKey,
      stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
            ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            stackAt s.sp allocHookStack ∗
            (((s.sp + 0x150#64) ↦₆₄ x.G.remoteIk.cap) ∗
              ((s.sp + 0x158#64) ↦₆₄ x.G.remoteIk.ptr) ∗
              vecU8Buf A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
              ((s.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗ ((s.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s.sp + 0x54#64) ↦₃₂ v54) ∗ ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ v60) ∗ ((s.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗ ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine seg_localIk hA hpc hrun hsp htr hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
            ((s1.sp + 0x178#64) ↦₆₄ 32#64) ∗
            stackAt s1.sp allocHookStack ∗
            (vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s1.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s1.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              ((s1.sp + 0x40#64) ↦₆₄ v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s1.sp + 0x54#64) ↦₃₂ v54) ∗ ((s1.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s1.sp + 0x60#64) ↦₆₄ v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s1.sp + 0x70#64) ↦₆₄ v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine seg_remoteIk hA hpc1 hrun1 hspA1 hx22_1 htr1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 hrem_b hrem_c => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            ((s2.sp + 0x48#64) ↦₆₄ v48) ∗
            stackAt s2.sp allocHookStack ∗
            (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              ((s2.sp + 0x40#64) ↦₆₄ v40) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s2.sp + 0x58#64) ↦₆₄ v58) ∗ ((s2.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s2.sp + 0x68#64) ↦₆₄ v68) ∗ ((s2.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s2.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecU8At_0x168_root_eq A s2.sp x.G.root.cap x.G.root.ptr x.st.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine seg_rootKey hA hpc2 hrun2 hspA2 hx28_2 htr2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  rw [← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s3.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s3.sp + 0x5f0#64) 104 ∗
            ((s3.sp + 0x40#64) ↦₆₄ v40) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗
            ((s3.sp + 0x58#64) ↦₆₄ v58) ∗ ((s3.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s3.sp + 0x68#64) ↦₆₄ v68) ∗ ((s3.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s3.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s3.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s3.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              ((s3.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  have hx20_3' : s3.readReg64 .x20 = localIk'.cap := by reg_chain
  have hx21_3' : s3.readReg64 .x21 = localIk'.ptr := by reg_chain
  have hx22_3' : s3.readReg64 .x22 = remoteIk'.cap := by reg_chain
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by reg_chain
  have hx23_3' : s3.readReg64 .x23 = s3.sp + 0x5f0#64 := by reg_chain
  refine seg_senderChain hsenderClone hpc3 hrun3 hspA3 hx20_3' hx21_3' hx22_3' hx26_3' hx23_3' hx28_3 htr3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hinl => ?_
  have hsp_eq : s3.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx23_4 ⊢
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by reg_chain) hspA4 hx23_4
      (by reg_chain)
      (by reg_chain)
      hx26_4
      (by reg_chain)
      htr4 hloc_b hloc_c hrem_b hrem_c hinl)

private theorem segClone_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_kernel

private theorem segClone_fields_5_to_9 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hchainClone : ChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 v08 v18 v30 : BitVec 64} {v14 v24 v28 v2c v3c : BitVec 32}
    {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x544#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x300#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = x.st.sessionVersion.setWidth 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
      (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32)
      (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32)
      (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' →
      s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = pendCap' →
      s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = chainsPtr' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
            (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
          optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗
          ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗
          OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗
          ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          ((s.sp + 0x30#64) ↦₆₄ chainsCap') ∗
          ((s.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
          (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
        vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
        optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗
        ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗
        ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecAt_0x180_chains_eq A s.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            (((s.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
              vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
              ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗
              ((s.sp + 0x14#64) ↦₃₂ v14) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
              ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₆₄ v30) ∗
              ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_receiverChains hA hchainClone x R s0 s ret Q _
    hpc hrun hsp hx26 htr hchains_len
    fun s1 chainsCap' chainsPtr' chains' hchains_l hchains_c hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
            ((s1.sp + 0x08#64) ↦₆₄ v08) ∗
            ((s1.sp + 0x18#64) ↦₆₄ v18) ∗
            ((s1.sp + 0x24#64) ↦₃₂ v24) ∗
            ((s1.sp + 0x28#64) ↦₃₂ v28) ∗
            ((s1.sp + 0x2c#64) ↦₃₂ v2c) ∗
            stackAt s1.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s1.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ v00) ∗ ((s1.sp + 0x14#64) ↦₃₂ v14) ∗
              ((s1.sp + 0x30#64) ↦₆₄ v30) ∗ ((s1.sp + 0x3c#64) ↦₃₂ v3c) ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len,
            stackAt_chainClone_eq_alloc s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_pendingPreKey hA hpc1 hrun1 hspA1 htr1
    fun s2 pendCap' pendPtr' v08' v24' v28' v2c' hpc2 hrun2 hsp2 hspA2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            (s2.sp ↦₆₄ v00) ∗
            ((s2.sp + 0x14#64) ↦₃₂ v14) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ v3c) ∗
            stackAt s2.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗
              vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
              ((s2.sp + 0x08#64) ↦₆₄ v08') ∗ ((s2.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s2.sp + 0x24#64) ↦₃₂ v24') ∗ ((s2.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s2.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s2.sp + 0x30#64) ↦₆₄ v30) ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_pendingKyber hA hpc2 hrun2 hspA2 htr2
    fun s3 kybCap' kybPtr' v14' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  have hx25_2' : (s2.readReg64 .x25).truncate 32 = x.st.sessionVersion := by
    rw [hx25_2, hx25_1, hx25, segClone_setWidth_64_truncate_32]
  rw [hx25_2', ← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗
            ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
            ((s3.sp + 0x30#64) ↦₆₄ v30) ∗
            stackAt s3.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              (s3.sp ↦₆₄ kybPtr') ∗ ((s3.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s3.sp + 0x14#64) ↦₃₂ v14') ∗ ((s3.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s3.sp + 0x24#64) ↦₃₂ v24') ∗ ((s3.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s3.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s3.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              memRegion (s3.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_aliceBaseKey hA hpc3 hrun3 hspA3 htr3
    fun s4 alice' hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 halice_b halice_c => ?_
  have hx26_3' : s3.readReg64 .x26 = chainsCap' := by reg_chain
  rw [hx26_3', ← hsp4]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (s4.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            stackAt s4.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s4.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s4.sp + 0x198#64) ∗
              optTailVecAt A 48 (s4.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s4.sp + 0x260#64) x.G.kyber ∗
              ((s4.sp + 0x288#64) ↦₃₂ w288) ∗ ((s4.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              (s4.sp ↦₆₄ kybPtr') ∗ ((s4.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s4.sp + 0x14#64) ↦₃₂ v14') ∗ ((s4.sp + 0x18#64) ↦₆₄ pendPtr') ∗
              ((s4.sp + 0x24#64) ↦₃₂ v24') ∗ ((s4.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s4.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s4.sp + 0x30#64) ↦₆₄ chainsCap') ∗
              ((s4.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s4.sp + 0x5f0#64) 104 ∗
              memRegion (s4.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  have hx24_4' : s4.readReg64 .x24 = s4.sp + 0xca0#64 := by reg_chain
  refine segClone_pqRatchet hA hpc4 hrun4 hspA4 hx24_4' htr4
    fun s5 pqCap' pqPtr' hpc5 hrun5 hsp5 hspA5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hpq_c => ?_
  have hsp_eq : s4.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx24_5 ⊢
  refine SepWPp.weaken_pre
    (by rw [stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl))
    (hnext s5 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc5 hrun5 (by reg_chain) hspA5
      (by reg_chain)
      hx20_5
      (by reg_chain)
      hx22_5
      (by reg_chain)
      hx24_5
      (by reg_chain)
      (by reg_chain)
      (by reg_chain)
      (by reg_chain)
      (by reg_chain)
      htr5 hchains_l hchains_c halice_b halice_c hpq_c)

private theorem segClone_fields_10_to_11 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (dv : DstVals)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (kybCap' kybPtr' v08 : BitVec 64) (w14 : BitVec 32) (pendCap' pendPtr' : BitVec 64)
    (w24 w28 w2c : BitVec 32) (w288 w28c : BitVec 32)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x594#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = kybCap')
    (hx20 : s.readReg64 .x20 = pqCap')
    (hx21 : s.readReg64 .x21 = w288.setWidth 64)
    (hx22 : s.readReg64 .x22 = pqPtr')
    (hx23 : s.readReg64 .x23 = w28c.setWidth 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (hx25 : s.readReg64 .x25 = alice'.cap)
    (hx26 : s.readReg64 .x26 = pendCap')
    (hx27 : s.readReg64 .x27 = alice'.ptr)
    (hx28 : s.readReg64 .x28 = chainsPtr')
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ s1 : State,
      s1.pc = (if x.st.version.toNat = x.msg.messageVersion.toNat then
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x69c#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x7e4#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x9 = x.msg.messageVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (segClone_dstSlotsWrittenAt s.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
          pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' w28 w2c v08 w24
          kybCap' kybPtr' w14 x.st.sessionVersion x.st.previousCounter w288 w28c ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
        Q (clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (dstSlotsAt s.sp dv ∗
        chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        spillSlotsAt s.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
          scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
          localIk'.ptr localIk'.cap ∗
        ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
      Q (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  refine segClone_assemble_1 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
    scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08 w14 pendPtr' w24 w28 w2c
    x.st.sessionVersion x.st.previousCounter
    (((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗ F)
    hpc hrun hsp hx24 hx28 htr
    fun s1 hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := segClone_dstSlotsMidAt s1.sp dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr'
            scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendPtr' ∗
          spillSlotsAt s1.sp kybPtr' v08 w14 pendPtr' w24 w28 w2c chainsCap' x.st.sessionVersion
            scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
            localIk'.ptr localIk'.cap ∗
          ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_assemble_2 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08 w14 pendCap' pendPtr'
    w24 w28 w2c w288 w28c
    (chunks96_6QAt (s1.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ F)
    hpc1 hrun1 hspA1 hx8_1 hx9_1 hx10_1
    (by reg_chain) (by reg_chain) (by reg_chain)
    (by reg_chain) (by reg_chain) hx24_1
    (by reg_chain) (by reg_chain) (by reg_chain) htr1
    fun s2 hpc2 hrun2 hsp2 hspA2 hx9_2 hx29_2 htr2 => ?_
  rw [hsp1]
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s2 hpc2 hrun2 (by reg_chain) hspA2 hx9_2 (by reg_chain) htr2)

private def segClone_clonePost (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧
    (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      recFrame A img x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      tapeAt ctl x.cur x.rest)

private theorem segClone_wp {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hchainClone : ChainCloneOkExt img.base A ext)
    (hsenderClone : SenderChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1a8#64)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h27 : s0.readReg64 .x27 = x.sret) (h19 : s0.readReg64 .x19 = x.remA)
    (h23 : s0.readReg64 .x23 = s0.sp + 0x5f0#64) (h24 : s0.readReg64 .x24 = s0.sp + 0xca0#64)
    (hrc32 : x.st.receiverChains.length < 2 ^ 32) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (if x.st.version.toNat = x.msg.messageVersion.toNat then
         (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x69c#64
       else
         (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x7e4#64)
      s0
      (memRegion s0.sp 0xa0 ∗
        ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
        memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool)
      (segClone_clonePost A ctl img x s0)
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hrc_lt : x.st.receiverChains.length < 2 ^ 63 := by omega
  rw [segClone_sessionStateAt_0x138_eq A s0.sp x.G x.st]
  refine SepWPp.weaken_pre
    (P' := ⌜PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
            (match x.st.remoteIdentity with
             | none => x.G.remoteIk.bytes = []
             | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) ∧
            x.G.chains.length = x.st.receiverChains.length ∧
            x.G.pending.isSome = x.st.pendingPreKey ∧ x.G.regIds.length = 8 ∧
            x.G.localIk.bytes.length = 33 ∧
            (x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)⌝ ∗
          (memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦ₛ x.G.regIds) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h28c : s0.sp + 0x288#64 + 4#64 = s0.sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (s0.sp + 0x288#64), h28c]
  refine SepWPp.weaken_pre
    (P' := memRegion s0.sp 0xa0 ∗
            ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗
            (A.pool ∗
              vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
              vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
              vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
              ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s0.sp + 0x28c#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine segClone_entry_combined hpc hrun hsp h19 h27 h23 h24 ⟨rfl, rfl⟩
    fun s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx23_1 hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
            vecU8At A (s1.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s1.sp + 0x5f0#64) 104 ∗
            ((s1.sp + 0x40#64) ↦₆₄ sv.v40) ∗
            ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗
            ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗
            ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗
            ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
            ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗
            ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
            ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s1.sp chainCloneStack ∗
            (((s1.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗
              ((s1.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗
              vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ sv.v00) ∗
              ((s1.sp + 0x08#64) ↦₆₄ sv.v08) ∗
              ((s1.sp + 0x14#64) ↦₃₂ sv.v14) ∗
              ((s1.sp + 0x18#64) ↦₆₄ sv.v18) ∗
              ((s1.sp + 0x24#64) ↦₃₂ sv.v24) ∗
              ((s1.sp + 0x28#64) ↦₃₂ sv.v28) ∗
              ((s1.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
              ((s1.sp + 0x30#64) ↦₆₄ sv.v30) ∗
              ((s1.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              memRegion (s1.sp + 0x10#64) 4 ∗
              memRegion (s1.sp + 0x20#64) 4 ∗
              memRegion (s1.sp + 0x38#64) 4 ∗
              memRegion (s1.sp + 0x50#64) 4 ∗
              dstSlotsAt s1.sp dv ∗
              ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              segClone_fixedRest A ctl img x s1.sp))
    (by unfold spillSlotsAt
        rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len,
            stackAt_chainClone_eq_alloc s1.sp]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_fields_1_to_4 hA hsenderClone hpc1 hrun1 hspA1 hx23_1 htr1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 htr2
      hloc_b hloc_c hrem_b hrem_c hinl => ?_
  rw [← hsp2] at hx23_2 ⊢
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0xca0#64 := by reg_chain
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗
            vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            ((s2.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
            (s2.sp ↦₆₄ sv.v00) ∗
            ((s2.sp + 0x08#64) ↦₆₄ sv.v08) ∗
            ((s2.sp + 0x14#64) ↦₃₂ sv.v14) ∗
            ((s2.sp + 0x18#64) ↦₆₄ sv.v18) ∗
            ((s2.sp + 0x24#64) ↦₃₂ sv.v24) ∗
            ((s2.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s2.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗
            ((s2.sp + 0x30#64) ↦₆₄ sv.v30) ∗
            ((s2.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            memRegion (s2.sp + 0x5f0#64) 104 ∗
            stackAt s2.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              optSenderChainHeap A sender' x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((s2.sp + 0x40#64) ↦₆₄ scCap') ∗
              ((s2.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s2.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
              ((s2.sp + 0x58#64) ↦₆₄ 32#64) ∗
              ((s2.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
              ((s2.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s2.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
              ((s2.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp + 0x10#64) 4 ∗
              memRegion (s2.sp + 0x20#64) 4 ∗
              memRegion (s2.sp + 0x38#64) 4 ∗
              memRegion (s2.sp + 0x50#64) 4 ∗
              dstSlotsAt s2.sp dv ∗
              ((s2.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              segClone_fixedRest A ctl img x s2.sp))
    (by rw [segClone_vecAt_0x180_chains_eq A s2.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_fields_5_to_9 hA hchainClone hpc2 hrun2 hspA2 hx24_2' hx25_2 hx26_2 htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3
      hchains_l hchains_c halice_b halice_c hpq_c => ?_
  rw [← hsp3] at hx24_3 ⊢
  refine SepWPp.weaken_pre
    (P' := dstSlotsAt s3.sp dv ∗
            chunks96_6QAt (s3.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            spillSlotsAt s3.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr localIk'.cap ∗
            ((s3.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            (A.pool ∗
              vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
                (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗
              vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
              ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
              vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
              optSenderChainHeap A sender' x.st.senderChain ∗
              OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗
              stackAt s3.sp chainCloneStack ∗
              segClone_fixedRest A ctl img x s3.sp))
    (by unfold spillSlotsAt; exact Entails.of_eq (by ac_rfl)) ?_
  refine segClone_fields_10_to_11 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08' v14' pendCap' pendPtr'
    v24' v28' v2c' w288 w28c _
    hpc3 hrun3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    fun s4 hpc4 hrun4 hsp4 hspA4 hx9_4 hx29_4 htr4 => ?_
  have hsp_eq : s3.sp = s0.sp := by reg_chain
  rw [hsp_eq]
  refine SepWPp.done hpc4 hrun4
    ⟨by reg_chain, hspA4, by reg_chain, htr4, hx9_4, ?_⟩
  have hdst :=
    segClone_dstSlotsWrittenAt_entails_sessionStateAt A s0.sp x localIk' remoteIk' rootPtr'
      chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
      sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
      kybCap' kybPtr' v14' w288 w28c
      h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
      hloc_b hloc_c hrem_b hrem_c hchains_l hchains_c halice_b halice_c hpq_c hinl
  have hsrc :=
    segClone_srcSessionState_reassemble A s0.sp x w288 w28c
      h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
  have hrest :=
    segClone_fixedRest_reassemble A ctl img x s0.sp sq0 sq1 sq2 sq3 sq4 sq5
      kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
      scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
      localIk'.ptr localIk'.cap
  rw [stackAt_chainClone_eq_alloc s0.sp]
  refine Entails.trans
    (Q := (segClone_dstSlotsWrittenAt s0.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
              pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
              kybCap' kybPtr' v14' x.st.sessionVersion x.st.previousCounter w288 w28c ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
            vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
            optSenderChainHeap A sender' x.st.senderChain ∗
            OptPendClone A x.G.pending pendCap' pendPtr' ∗
            OptKybClone A x.G.kyber kybCap' kybPtr') ∗
          (vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗
            vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗
            vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗
            optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s0.sp + 0x28c#64) ↦₃₂ w28c)) ∗
          (spillSlotsAt s0.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap
              localIk'.ptr localIk'.cap ∗
            chunks96_6QAt (s0.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            memRegion (s0.sp + 0x5f0#64) 104 ∗
            ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
            stackAt s0.sp allocHookStack ∗ A.pool ∗
            segClone_fixedRest A ctl img x s0.sp))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hdst (sepConj_mono hsrc hrest)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G₁
  refine Entails.sepExists_right G₁ ?_
  exact Entails.of_eq (by ac_rfl)

/-- From `recordRegionEntry img` (`+0x1a8`) under `recordDecryptSpec.pre`, execution clones the
session and reaches `VState` (`+0x69c`) when versions match, `MState` (`+0x7e4`) on version mismatch,
or panics on allocation failure. -/
theorem segClone_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    SegCloneSpecExt img C A ctl uuidTryParse S ext := by
  intro hloads hhooks hchainClone hsenderClone x R s0 hpc hrun hpre hL
  have hentry_eq :
      entryOf img msgDecryptName = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName :=
    entryOf_eq_tripleRatchetProgAtExt ext hloads msgDecryptName
  have hpc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x1a8#64 := by
    simpa [recordRegionEntry, hentry_eq] using hpc
  dsimp only [recordDecryptSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hF, hsym⟩, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_ne, hseeds, hrc32, _⟩, hm⟩ := hpre
  have hwp :=
    segClone_wp (C := C) (ctl := ctl) (S := S)
      hhooks.toAllocContracts hchainClone hsenderClone x R s0
      hpc' hrun hsp h27 h19 h23 h24 hrc32
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMeta img s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf, hF.of_keepsFrozen hsteps.keepsFrozen, hsteps.symtab_eq.trans hsym, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'
    obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
    obtain ⟨hclone, hmf'⟩ := hmf'
    simp only [sepConj_assoc] at hmf'
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = recVPC img := by simpa [recVPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inl ⟨G₁, hpcV, hmeta, ⟨hrem_ne, hseeds, hrc32⟩, hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = recMPC img := by simpa [recMPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem segClone_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    SegCloneSpec img C A ctl uuidTryParse S abs :=
  fun hloads hhooks => segClone_ok_ext hloads (Stage2Contracts.of_tripleRatchetProgAt' hhooks)

end CryptoVerification.LibsignalTripleRatchet.Record
