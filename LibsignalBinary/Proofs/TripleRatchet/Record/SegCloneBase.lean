/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.FetchClone
import ProofLib.SepLogic.WPp

/-!
# Shared Definitions and Layout Helpers for `SegClone`

Callee address bridges, panic-tail lemmas, 128-byte stack spill layout (`spillSlotsAt`), and
344-byte destination `SessionStructure` slot decompositions (`dstSlotsAtRaw`) for `SegClone`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Extern hooks, callee address bridges, and panic tails -/

theorem segClone_shim_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
      sessionShimSpec :=
  hA.shim_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

theorem segClone_alloc_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at msgDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

theorem segClone_memcpy_ok_at {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at msgDecryptName (num% (ls_off% "memcpy" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

theorem segClone_panic_at_handle_error {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal")) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext msgDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
    (by fnoff_eq)

theorem fnAddr_msgDecrypt_to_chainClone {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")) =
      (tripleRatchetProgAtExt b ext).fnAddr chainCloneName := by
  change (b + BitVec.ofNat 64 (libsignalSessionCode.fnOff msgDecryptName)) + bv% (2 ^ 64 - 8252) =
    b + BitVec.ofNat 64 (libsignalSessionCode.fnOff chainCloneName)
  rw [libsignalSessionCode_fnOff_sym_3a4a8, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]")]
  bv_omega

theorem segClone_chainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcc : ChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")))
      (chainCloneSpec A) := by
  rwa [fnAddr_msgDecrypt_to_chainClone]

theorem segClone_senderChainClone_ok_at {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hscc : SenderChainCloneOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr msgDecryptName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#2]") - (ls_off% "session_message_decrypt_signal")))
      (senderChainCloneSpec A) := by
  rwa [fnAddr_msgDecrypt_to_chainClone]

abbrev clonePanicPost (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
    (sf.mem ⊨ (recordDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R)

theorem onPanic_of_allocFailed {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : RecordDecryptGhost} {R P_f : SepProp} {s0 sf : State}
    (halloc : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)
    (hm : sf.mem ⊨ P_f ∗ R) :
    sf.mem ⊨ (recordDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  simpa only [recordDecryptSpec, Spec.inImage, sepConj_assoc] using
    allowPanic_panicked ⟨Or.inr (Or.inr halloc.1), halloc.2⟩ hm

theorem allocFailedIn_of_eq {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem segClone_panic_0x25f8 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x25f8#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x25f8 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2604 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2604#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x2604 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2610 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2610#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x2610 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x261c {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x261c#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x261c 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2628 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2628#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x2628 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

theorem segClone_panic_0x2634 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (x : RecordDecryptGhost) (s0 s : State) (P R : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr msgDecryptName + 0x2634#64)
    (hrun : s.status = .Running)
    (htrace : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_3a4a8
  have hpanic := segClone_panic_at_handle_error (b := img.base) (ext := ext)
  segClone_fetches img.base (Rust.withPanics ext) hfn 0x2634 12
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "session_message_decrypt_signal"))
  wp_steps
  refine SepWP.done rfl hrun ?_
  refine SepWPp.panic hrun hpanic fun hm => ?_
  exact onPanic_of_allocFailed (allocFailedIn_of_eq (by simp only [State.setPC, State.writeReg64, Rust.panicked, htrace])) hm

/-! ## Arithmetic, byte-slice, and `Vec<u8>` helpers -/

theorem srk_length_pos {bs : List (BitVec 8)} {pk : PublicKey}
    (h : PublicKey.deserialize bs = .ok pk) : 0 < bs.length := by
  cases bs with
  | nil => nomatch h
  | cons _ _ => exact Nat.succ_pos _

theorem ofNat_ne_zero_of_pos {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64] at ht
  change n = 0 at ht
  omega

theorem beq_ofNat_zero_eq_false {n : Nat} (hpos : 0 < n) (h64 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact ofNat_ne_zero_of_pos hpos h64

theorem cap_add_one_ne_zero {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add] at ht
  change (cap.toNat + 1) % 2 ^ 64 = 0 at ht
  rw [Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact cap_add_one_ne_zero hlt

theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

theorem segClone_pure_eq_emp {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  rw [propext ⟨fun _ => trivial, fun _ => h⟩]; simp

theorem vecU8Buf_pure_extract (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  apply ProofLib.sepProp_eq_of_entails
  · apply Entails.pure_left; intro hp
    exact Entails.pure_right hp (Entails.pure_right hp (Entails.refl _))
  · exact Entails.pure_left fun _ => Entails.refl _

theorem vecU8At_eq_of_nil (A : RustAlloc) (a cap ptr : BitVec 64) :
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

theorem vecU8At_eq_of_pos (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8))
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

theorem vecGhostAt_eq_of_nil (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hnil : g.bytes = []) :
    vecGhostAt A g a =
      ⌜g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗
      vecU8Buf A g.cap g.ptr [] := by
  unfold vecGhostAt
  rw [hnil, vecU8At_eq_of_nil]

theorem vecGhostAt_eq_of_pos (A : RustAlloc) (g : VecGhost) (a : BitVec 64)
    (hpos : 0 < g.bytes.length) :
    vecGhostAt A g a =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      (g.ptr ↦ₛ g.bytes) ∗ A.live g.ptr g.cap.toNat 1 ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) :=
  vecU8At_eq_of_pos A a g.cap g.ptr g.bytes hpos

theorem vecU8Buf_nil_eq (A : RustAlloc) :
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

theorem vecU8Buf_pos_eq (A : RustAlloc) (ptr' : BitVec 64) (bs : List (BitVec 8))
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

theorem stackAt_root_eq_chainClone (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗
        stackAt sp chainCloneStack := by
  have h := stackAt_split_bottom sp chainCloneStack (rootStack - chainCloneStack) (by decide)
  rwa [show chainCloneStack + (rootStack - chainCloneStack) = rootStack by decide] at h

theorem stackAt_chainClone_eq_alloc (sp : BitVec 64) :
    stackAt sp chainCloneStack =
      memRegion (sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack 208 (by decide)
  rwa [show allocHookStack + 208 = chainCloneStack by decide] at h

/-! ## Stack frame, spill slots, and field decomposition lemmas -/

theorem elim_region8 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 8 + rem) (hb : b' = b + 8#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 64, (memRegion b' rem ∗ (b ↦₆₄ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₆₄ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₆₄ v) ∗ F by ac_rfl]
  exact h v

theorem elim_region4 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 4 + rem) (hb : b' = b + 4#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 32, (memRegion b' rem ∗ (b ↦₃₂ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₃₂ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₃₂ v) ∗ F by ac_rfl]
  exact h v

theorem elim_region1 {b b' : BitVec 64} {n rem : Nat} {F Q : SepProp}
    (hn : n = 1 + rem) (hb : b' = b + 1#64) (hle : n ≤ 2 ^ 64)
    (h : ∀ v : BitVec 8, (memRegion b' rem ∗ (b ↦₈ v) ∗ F) ⊢ Q) :
    (memRegion b n ∗ F) ⊢ Q := by
  rw [memRegion_split' hn hb hle, memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro v
  rw [show ((b ↦₈ v) ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ (b ↦₈ v) ∗ F by ac_rfl]
  exact h v

theorem elim_region_skip {b b' : BitVec 64} {N n rem : Nat} {F Q : SepProp}
    (hN : N = n + rem) (hb : b' = b + BitVec.ofNat 64 n) (hle : N ≤ 2 ^ 64)
    (h : (memRegion b' rem ∗ memRegion b n ∗ F) ⊢ Q) :
    (memRegion b N ∗ F) ⊢ Q := by
  rw [memRegion_split' hN hb hle]
  rw [show (memRegion b n ∗ memRegion b' rem) ∗ F = memRegion b' rem ∗ memRegion b n ∗ F by ac_rfl]
  exact h

theorem elim_region96_6Q {b b' : BitVec 64} {N rem : Nat} {F Q : SepProp}
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

/-- Spatial layout of the 128-byte spill area `sp .. sp + 0x80`. -/
def spillSlotsAt (sp : BitVec 64)
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

theorem memRegion_0x80_entails_spillSlotsAt_gen {α : Type} (sp : BitVec 64)
    (mk : BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 →
          BitVec 32 → BitVec 32 → BitVec 32 → BitVec 64 → BitVec 32 →
          BitVec 64 → BitVec 64 → BitVec 32 → BitVec 64 → BitVec 64 →
          BitVec 64 → BitVec 64 → BitVec 64 → α)
    (P : α → SepProp)
    (hP : ∀ v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78,
      P (mk v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78) =
        spillSlotsAt sp v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78) :
    memRegion sp 0x80 ⊢ ∃∗ sv : α, P sv := by
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
    (mk v00 v08 v14 v18 v24 v28 v2c v30 v3c v40 v48 v54 v58 v60 v68 v70 v78) ?_
  rw [hP]
  unfold spillSlotsAt
  exact Entails.of_eq (by ac_rfl)

theorem spillSlotsAt_entails_memRegion_0x80 (sp : BitVec 64)
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

theorem memRegion_0x80_0x20_entails (sp : BitVec 64) :
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

theorem memRegion_0x5b0_0x40_entails (sp : BitVec 64) :
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

theorem memRegion_0x5f0_0x6b0_eq (sp : BitVec 64) :
    memRegion (sp + 0x5f0#64) 0x6b0 =
      memRegion (sp + 0x5f0#64) 104 ∗
      memRegion (sp + 0x658#64) 0x4e8 ∗
      memRegion (sp + 0xb40#64) 96 ∗
      memRegion (sp + 0xba0#64) 0x100 := by
  rw [memRegion_split' (b := sp + 0x5f0#64) (b' := sp + 0x658#64) (n := 104) (k := 1608) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0x658#64) (b' := sp + 0xb40#64) (n := 0x4e8) (k := 352) rfl (by bv_arith) (by decide),
      memRegion_split' (b := sp + 0xb40#64) (b' := sp + 0xba0#64) (n := 96) (k := 0x100) rfl (by bv_arith) (by decide)]

theorem chunks96_6QAt_entails_memRegion (base : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt base q0 q1 q2 q3 q4 q5 ⊢ memRegion base 96 := by
  rw [chunks96_6QAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion base (bytes96Of6Q q0 q1 q2 q3 q4 q5)
  rwa [bytes96Of6Q_length] at h

theorem exists_unpack32_of_length_4 {bs : List (BitVec 8)} (h : bs.length = 4) :
    ∃ v : BitVec 32, bs = unpack32 v := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;>
    try (simp at h)
  refine ⟨b3 ++ b2 ++ b1 ++ b0, ?_⟩
  simp only [unpack32, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem exists_unpack32_pair_of_length_8 {bs : List (BitVec 8)} (h : bs.length = 8) :
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

theorem exists_tail24_decomp {bs : List (BitVec 8)} (h : bs.length = 24) :
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

def OptPendClone (A : RustAlloc) (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) : SepProp :=
  match orig with
  | none => ⌜pendCap' = noneCap⌝
  | some gp =>
    ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
      vecU8Buf A pendCap' pendPtr' gp.vec.bytes

def OptKybClone (A : RustAlloc) (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) : SepProp :=
  match orig with
  | none => ⌜kybCap' = noneCap⌝
  | some gk =>
    ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
      vecU8Buf A kybCap' kybPtr' gk.vec.bytes

theorem optTailVecAt_48_of_optPendClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost)
    (pendCap' pendPtr' : BitVec 64) (w28 w2c : BitVec 32) (v08 : BitVec 64) (w24 : BitVec 32) :
    ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
      ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
      ((a + 40#64) ↦₃₂ w24) ∗ memRegion (a + 44#64) 4 ∗
      OptPendClone A orig pendCap' pendPtr') ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = orig.isSome⌝ ∗ optTailVecAt A 48 a pend' := by
  cases orig with
  | none =>
    dsimp only [OptPendClone]
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
          ((a + 40#64) ↦₃₂ w24) ∗ memRegion (a + 44#64) 4 ∗ ⌜pendCap' = noneCap⌝) =
        (⌜pendCap' = noneCap⌝ ∗ (a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗
          ((a + 16#64) ↦₆₄ pendCap') ∗ ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗
          ((a + 32#64) ↦₆₄ v08) ∗ ((a + 40#64) ↦₃₂ w24) ∗ memRegion (a + 44#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    apply Entails.pure_right rfl
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 32) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 24) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 20) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 28#64) (b' := a + 32#64) (n := 4) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 32#64) (b' := a + 40#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 40#64) (b' := a + 44#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gp =>
    dsimp only [OptPendClone]
    rw [memRegion_four (a + 44#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w4
    rw [show ((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap') ∗
          ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
          ((a + 40#64) ↦₃₂ w24) ∗ ((a + 44#64) ↦₃₂ w4) ∗
          ⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
          vecU8Buf A pendCap' pendPtr' gp.vec.bytes) =
        (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗
          (((a ↦₆₄ pendCap') ∗ ((a + 8#64) ↦₆₄ pendPtr') ∗ ((a + 16#64) ↦₆₄ pendCap')) ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
            ((a + 40#64) ↦₃₂ w24) ∗ ((a + 44#64) ↦₃₂ w4))) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    set tail := unpack32 w28 ++ unpack32 w2c ++ unpack64 v08 ++ unpack32 w24 ++ unpack32 w4
    have htail_len : tail.length = 24 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ w28) ∗ ((a + 28#64) ↦₃₂ w2c) ∗ ((a + 32#64) ↦₆₄ v08) ∗
          ((a + 40#64) ↦₃₂ w24) ∗ ((a + 44#64) ↦₃₂ w4) := by
      unfold tail
      simp only [List.append_assoc, pointsToBytes_append, unpack32_length, unpack64_length,
        ← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      have h32 : a + 28#64 + BitVec.ofNat 64 4 = a + 32#64 := by bv_arith
      have h40 : a + 32#64 + BitVec.ofNat 64 8 = a + 40#64 := by bv_arith
      have h44 : a + 40#64 + BitVec.ofNat 64 4 = a + 44#64 := by bv_arith
      rw [h28, h32, h40, h44]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gp.vec.bytes.length, pendPtr', gp.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    apply Entails.pure_right rfl
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

theorem optTailVecAt_32_of_optKybClone (A : RustAlloc) (a : BitVec 64)
    (orig : Option TailVecGhost)
    (kybCap' kybPtr' : BitVec 64) (w14 : BitVec 32) :
    ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
      ((a + 24#64) ↦₃₂ w14) ∗ memRegion (a + 28#64) 4 ∗
      OptKybClone A orig kybCap' kybPtr') ⊢
      ∃∗ kyb' : Option TailVecGhost, optTailVecAt A 32 a kyb' := by
  cases orig with
  | none =>
    dsimp only [OptKybClone]
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ w14) ∗ memRegion (a + 28#64) 4 ∗ ⌜kybCap' = noneCap⌝) =
        (⌜kybCap' = noneCap⌝ ∗ (a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗
          ((a + 16#64) ↦₆₄ kybCap') ∗ ((a + 24#64) ↦₃₂ w14) ∗ memRegion (a + 28#64) 4) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    refine Entails.sepExists_right none ?_
    unfold optTailVecAt
    apply sepConj_mono_right
    rw [memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 16#64) (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_arith) (by decide),
        memRegion_split' (b := a + 24#64) (b' := a + 28#64) (n := 4) (k := 4) rfl (by bv_arith) (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo64_entails_memRegion _ _) <|
      sepConj_mono (pointsTo32_entails_memRegion _ _) (Entails.refl _)
  | some gk =>
    dsimp only [OptKybClone]
    rw [memRegion_four (a + 28#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    rw [show ((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap') ∗
          ((a + 24#64) ↦₃₂ w14) ∗ ((a + 28#64) ↦₃₂ w1) ∗
          ⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
          vecU8Buf A kybCap' kybPtr' gk.vec.bytes) =
        (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗
          (((a ↦₆₄ kybCap') ∗ ((a + 8#64) ↦₆₄ kybPtr') ∗ ((a + 16#64) ↦₆₄ kybCap')) ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (((a + 24#64) ↦₃₂ w14) ∗ ((a + 28#64) ↦₃₂ w1))) by ac_rfl]
    apply Entails.pure_left; rintro rfl
    set tail := unpack32 w14 ++ unpack32 w1
    have htail_len : tail.length = 8 := by simp [tail]
    have htail_eq :
        ((a + 24#64) ↦ₛ tail) =
          ((a + 24#64) ↦₃₂ w14) ∗ ((a + 28#64) ↦₃₂ w1) := by
      unfold tail
      rw [pointsToBytes_append, unpack32_length,
          ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
      have h28 : a + 24#64 + BitVec.ofNat 64 4 = a + 28#64 := by bv_arith
      rw [h28]
    rw [← htail_eq]
    set g' : TailVecGhost := ⟨⟨BitVec.ofNat 64 gk.vec.bytes.length, kybPtr', gk.vec.bytes⟩, tail⟩
    refine Entails.sepExists_right (some g') ?_
    unfold optTailVecAt
    apply Entails.pure_right htail_len
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    exact Entails.refl _

/-- Spatial layout of the 344-byte destination `SessionStructure` slot at `sp + 0xca0`,
parameterized directly by field values. -/
def dstSlotsAtRaw (sp : BitVec 64)
    (w_ca0 w_ca8 w_cb0 w_cb8 w_cc0 w_cc8 w_cd0 w_cd8 w_ce0 w_ce8 w_cf0 w_cf8
     w_d00 w_d08 w_d10 w_d18 w_d20 w_d28 w_d30 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128)
    (w_d98 w_da0 w_da8 : BitVec 64) (w_db0 w_db4 : BitVec 32) (w_db8 : BitVec 64)
    (w_dc0 : BitVec 32) (w_dc8 w_dd0 w_dd8 : BitVec 64)
    (w_de0 w_de8 w_dec w_df0 w_df4 : BitVec 32) : SepProp :=
  ((sp + 0xca0#64) ↦₆₄ w_ca0) ∗ ((sp + 0xca8#64) ↦₆₄ w_ca8) ∗ ((sp + 0xcb0#64) ↦₆₄ w_cb0) ∗
  ((sp + 0xcb8#64) ↦₆₄ w_cb8) ∗ ((sp + 0xcc0#64) ↦₆₄ w_cc0) ∗ ((sp + 0xcc8#64) ↦₆₄ w_cc8) ∗
  ((sp + 0xcd0#64) ↦₆₄ w_cd0) ∗ ((sp + 0xcd8#64) ↦₆₄ w_cd8) ∗ ((sp + 0xce0#64) ↦₆₄ w_ce0) ∗
  ((sp + 0xce8#64) ↦₆₄ w_ce8) ∗ ((sp + 0xcf0#64) ↦₆₄ w_cf0) ∗ ((sp + 0xcf8#64) ↦₆₄ w_cf8) ∗
  ((sp + 0xd00#64) ↦₆₄ w_d00) ∗ ((sp + 0xd08#64) ↦₆₄ w_d08) ∗ ((sp + 0xd10#64) ↦₆₄ w_d10) ∗
  ((sp + 0xd18#64) ↦₆₄ w_d18) ∗ ((sp + 0xd20#64) ↦₆₄ w_d20) ∗ ((sp + 0xd28#64) ↦₆₄ w_d28) ∗
  ((sp + 0xd30#64) ↦₆₄ w_d30) ∗
  chunks96_6QAt (sp + 0xd38#64) q0 q1 q2 q3 q4 q5 ∗
  ((sp + 0xd98#64) ↦₆₄ w_d98) ∗ ((sp + 0xda0#64) ↦₆₄ w_da0) ∗ ((sp + 0xda8#64) ↦₆₄ w_da8) ∗
  ((sp + 0xdb0#64) ↦₃₂ w_db0) ∗ ((sp + 0xdb4#64) ↦₃₂ w_db4) ∗ ((sp + 0xdb8#64) ↦₆₄ w_db8) ∗
  ((sp + 0xdc0#64) ↦₃₂ w_dc0) ∗ memRegion (sp + 0xdc4#64) 4 ∗
  ((sp + 0xdc8#64) ↦₆₄ w_dc8) ∗ ((sp + 0xdd0#64) ↦₆₄ w_dd0) ∗ ((sp + 0xdd8#64) ↦₆₄ w_dd8) ∗
  ((sp + 0xde0#64) ↦₃₂ w_de0) ∗ memRegion (sp + 0xde4#64) 4 ∗
  ((sp + 0xde8#64) ↦₃₂ w_de8) ∗ ((sp + 0xdec#64) ↦₃₂ w_dec) ∗
  ((sp + 0xdf0#64) ↦₃₂ w_df0) ∗ ((sp + 0xdf4#64) ↦₃₂ w_df4)

theorem memRegion_344_entails_dstSlotsAt_gen {α : Type} (sp : BitVec 64)
    (mk : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
          BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
          BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
          BitVec 64 →
          BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128 →
          BitVec 64 → BitVec 64 → BitVec 64 → BitVec 32 → BitVec 32 → BitVec 64 →
          BitVec 32 → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 32 →
          BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 → α)
    (P : α → SepProp)
    (hP : ∀ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
            q0 q1 q2 q3 q4 q5 w_d98 w_da0 w_da8 w_db0 w_db4 w_db8 w_dc0
            w_dc8 w_dd0 w_dd8 w_de0 w_de8 w_dec w_df0 w_df4,
      P (mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
            q0 q1 q2 q3 q4 q5 w_d98 w_da0 w_da8 w_db0 w_db4 w_db8 w_dc0
            w_dc8 w_dd0 w_dd8 w_de0 w_de8 w_dec w_df0 w_df4) =
        dstSlotsAtRaw sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
          q0 q1 q2 q3 q4 q5 w_d98 w_da0 w_da8 w_db0 w_db4 w_db8 w_dc0
          w_dc8 w_dd0 w_dd8 w_de0 w_de8 w_dec w_df0 w_df4) :
    memRegion (sp + 0xca0#64) 344 ⊢ ∃∗ dv : α, P dv := by
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
    (mk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
      q0 q1 q2 q3 q4 q5 w_d98 w_da0 w_da8 w_db0 w_db4 w_db8 w_dc0
      w_dc8 w_dd0 w_dd8 w_de0 w_de8 w_dec w_df0 w_df4) ?_
  rw [hP]
  unfold dstSlotsAtRaw
  exact Entails.of_eq (by ac_rfl)

def signalMessageRestAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
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

theorem signalMessageAt_eq_ver (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      (((a + 0x70#64) ↦₈ m.messageVersion) ∗ signalMessageRestAt A g a m) := by
  unfold signalMessageAt signalMessageRestAt
  ac_rfl

/-! ## Shared helpers for sub-segments and reassembly -/

@[simp, arm64_norm]
theorem int64_toBitVec_mk (u : UInt64) :
    ({ toUInt64 := u } : Int64).toBitVec = u.toBitVec := rfl

@[simp, arm64_norm]
theorem uint64_toBitVec_mk (v : BitVec 64) :
    ({ toBitVec := v } : UInt64).toBitVec = v := rfl

@[simp, arm64_norm]
theorem uint64_toBitVec_ofNat (n : Nat) :
    (OfNat.ofNat n : UInt64).toBitVec = BitVec.ofNat 64 n := rfl

theorem eq_nil_or_length_pos {α : Type} (l : List α) : l = [] ∨ 0 < l.length := by
  cases l with
  | nil => exact Or.inl rfl
  | cons _ _ => exact Or.inr (Nat.zero_lt_succ _)

theorem sepWPp_pure_2nd {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2) Q Qp) :
    SepWPp prog ret s (P1 ∗ ⌜φ⌝ ∗ P2) Q Qp := by
  rw [show P1 ∗ ⌜φ⌝ ∗ P2 = ⌜φ⌝ ∗ P1 ∗ P2 by ac_rfl]
  exact SepWPp.pure_elim h

theorem sepWPp_pure_3rd {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp := by
  rw [show P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 by ac_rfl]
  exact SepWPp.pure_elim h

theorem entails_pure_2nd {P1 P2 P3 : SepProp} {φ : Prop}
    (hφ : φ) (heq : P1 = P2 ∗ P3) :
    P1 ⊢ P2 ∗ ⌜φ⌝ ∗ P3 := by
  rw [heq, show P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P2 ∗ P3 by ac_rfl]
  exact Entails.pure_right hφ (Entails.refl _)

def optSenderChainSomeRest (A : RustAlloc) (a : BitVec 64)
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

theorem optSenderChainAt_some_eq_cap (A : RustAlloc) (a : BitVec 64)
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

theorem chunks104W6QAt_entails_memRegion (a : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt a w0 q0 q1 q2 q3 q4 q5 ⊢ memRegion a 104 := by
  rw [chunks104W6QAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a (bytes104OfW6Q w0 q0 q1 q2 q3 q4 q5)
  rwa [bytes104OfW6Q_length] at h

theorem chunks104W6QAt_sp_0x5f0 (sp : BitVec 64) (w0 : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks104W6QAt (sp + 0x5f0#64) w0 q0 q1 q2 q3 q4 q5 =
      ((sp + 0x5f0#64) ↦₆₄ w0) ∗
      (((sp + 0x5f0#64) + 0x8#64) ↦₁₂₈ q0) ∗
      (((sp + 0x5f0#64) + 0x18#64) ↦₁₂₈ q1) ∗
      (((sp + 0x5f0#64) + 0x28#64) ↦₁₂₈ q2) ∗
      (((sp + 0x5f0#64) + 0x38#64) ↦₁₂₈ q3) ∗
      (((sp + 0x5f0#64) + 0x48#64) ↦₁₂₈ q4) ∗
      (((sp + 0x5f0#64) + 0x58#64) ↦₁₂₈ q5) := rfl

theorem chunks96_6QAt_sp_0xb40 (sp : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
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

theorem onPanic_of_callee_panic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
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

theorem segClone_off_add_succ_mul_104 (off : BitVec 64) (k : Nat) :
    off + BitVec.ofNat 64 (k + 1) * 104#64 =
      (off + 0x68#64) + BitVec.ofNat 64 k * 104#64 := by
  rw [BitVec.ofNat_add]
  bv_arith

theorem segClone_bv_ofNat_mul_104_toNat {n : Nat} (hlt : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n * 104#64).toNat = n * 104 := by
  have hn : n < 2 ^ 64 := by omega
  have hprod : n * 104 < 2 ^ 64 := by omega
  change ((BitVec.ofNat 64 n).toNat * (104#64 : BitVec 64).toNat) % 2 ^ 64 = n * 104
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  change (n * 104) % 2 ^ 64 = n * 104
  exact Nat.mod_eq_of_lt hprod

def segClone_vecBufRest {α : Type} (A : RustAlloc) (stride align : Nat)
    (cap ptr : BitVec 64) (xs : List α) : SepProp :=
  ⌜xs.length ≤ cap.toNat ∧ cap.toNat * stride < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  (if cap = 0 then emp
   else A.live ptr (cap.toNat * stride) align ∗
     memRegion (ptr + BitVec.ofNat 64 (xs.length * stride)) ((cap.toNat - xs.length) * stride))

theorem segClone_vecBuf_expose_arrayAt {α : Type} (A : RustAlloc) {stride : Nat}
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

theorem segClone_vecBuf_reassemble_arrayAt {α : Type} (A : RustAlloc) (stride align : Nat)
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

theorem segClone_vecBuf_chain_nil_eq (A : RustAlloc) :
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

theorem segClone_vecBuf_chain_of_arrayAt (A : RustAlloc) (ptr' : BitVec 64)
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

/-! ## Destination `SessionStructure` layouts and helpers -/

def segClone_dstSlotsWrittenAt (sp : BitVec 64)
    (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
    (chainsCap' chainsPtr' : BitVec 64) (alice' : VecGhost)
    (pqCap' pqPtr' : BitVec 64)
    (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128)
    (pendCap' pendPtr' : BitVec 64) (w28 w2c : BitVec 32) (v08 : BitVec 64) (w24 : BitVec 32)
    (kybCap' kybPtr' : BitVec 64) (w14 : BitVec 32)
    (sessVer prevCnt w288 w28c : BitVec 32) : SepProp :=
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
  ((sp + 0xde8#64) ↦₃₂ sessVer) ∗ ((sp + 0xdec#64) ↦₃₂ prevCnt) ∗
  ((sp + 0xdf0#64) ↦₃₂ w288) ∗ ((sp + 0xdf4#64) ↦₃₂ w28c)

theorem segClone_sessionStateAt_0x138_eq (A : RustAlloc) (sp : BitVec 64)
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

theorem segClone_memRegion_0xa0_eq (sp : BitVec 64) :
    memRegion sp 0xa0 = memRegion sp 0x80 ∗ memRegion (sp + 0x80#64) 0x20 :=
  memRegion_split' (b := sp) (b' := sp + 0x80#64) (n := 0x80) (k := 0x20) rfl rfl (by decide)

theorem segClone_memRegion_0x4b0_0x950_eq (sp : BitVec 64) :
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

theorem segClone_vecGhostAt_0x138_eq (A : RustAlloc) (g : VecGhost) (sp : BitVec 64) :
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

theorem segClone_vecGhostAt_0x150_eq (A : RustAlloc) (g : VecGhost) (sp : BitVec 64) :
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

theorem segClone_vecU8At_0x168_root_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
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

theorem segClone_vecAt_0x180_chains_eq (A : RustAlloc) (sp cap ptr : BitVec 64)
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

def segClone_fixedRest (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
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

theorem segClone_fixedRest_reassemble (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
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

theorem segClone_srcSessionState_reassemble (A : RustAlloc) (sp : BitVec 64)
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

theorem segClone_version_cond_iff (sv : BitVec 32) (mv : BitVec 8) :
    ((if sv = 0 then 2#64 else BitVec.truncate 64 sv) = BitVec.zeroExtend 64 mv) ↔
      (if sv = 0 then 2 else sv) = mv.setWidth 32 := by
  bv_kernel

theorem segClone_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by
  bv_kernel

theorem pointsTo128_eq_pointsTo64 (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) = ((a ↦₆₄ v.extractLsb' 0 64) ∗ ((a + 8#64) ↦₆₄ v.extractLsb' 64 64)) := by
  unfold pointsTo128; rfl

theorem cat128_extractLsb (v : BitVec 128) :
    v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by bv_kernel

theorem chunks104_6QWAt_sp_0x5f0 (sp : BitVec 64)
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

theorem chunks104_6QWAt_entails_memRegion (a : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt a q0 q1 q2 q3 q4 q5 w6 ⊢ memRegion a 104 := by
  rw [chunks104_6QWAt_eq_pointsToBytes]
  have h := pointsToBytes_entails_memRegion a (bytes104Of6QW q0 q1 q2 q3 q4 q5 w6)
  rwa [bytes104Of6QW_length] at h

theorem memRegion_104_entails_chunks104_6QWAt (a : BitVec 64) :
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

theorem segClone_bv_ofNat_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  have h : BitVec.ofNat 64 (n + 1) = BitVec.ofNat 64 n + 1#64 := BitVec.ofNat_add n 1
  rw [h]; bv_arith

theorem segClone_bv_ofNat_mul_104 {n : Nat} :
    BitVec.ofNat 64 n * 104#64 = BitVec.ofNat 64 (n * 104) := by
  simpa using (BitVec.ofNat_mul n 104).symm

theorem segClone_bv_ofNat_mul_104_beq_zero {n : Nat} (hpos : 0 < n) (hlt : n * 104 < 2 ^ 63) :
    (BitVec.ofNat 64 n * 104#64 == 0#64) = false := by
  rw [segClone_bv_ofNat_mul_104]
  exact beq_ofNat_zero_eq_false (by omega) (by omega)

theorem segClone_dstSlotsWrittenAt_entails_sessionStateAt
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
  have hloc_hdr :
      ((sp + 0xca0#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xca8#64) ↦₆₄ localIk'.ptr) ∗
        ((sp + 0xcb0#64) ↦₆₄ localIk'.cap) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes =
      vecGhostAt A localIk' (sp + 0xca0#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h1 : sp + 0xca0#64 + 8#64 = sp + 0xca8#64 := by bv_arith
    have h2 : sp + 0xca0#64 + 16#64 = sp + 0xcb0#64 := by bv_arith
    have h3 : BitVec.ofNat 64 localIk'.bytes.length = localIk'.cap := by
      rw [hloc_bytes, ← hloc_cap]
    rw [h1, h2, h3]
    ac_rfl
  have hrem_hdr :
      ((sp + 0xcb8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xcc0#64) ↦₆₄ remoteIk'.ptr) ∗
        ((sp + 0xcc8#64) ↦₆₄ remoteIk'.cap) ∗
        vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes =
      vecGhostAt A remoteIk' (sp + 0xca0#64 + 0x18#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xca0#64 + 0x18#64 = sp + 0xcb8#64 := by bv_arith
    have h1 : sp + 0xcb8#64 + 8#64 = sp + 0xcc0#64 := by bv_arith
    have h2 : sp + 0xcb8#64 + 16#64 = sp + 0xcc8#64 := by bv_arith
    have h3 : BitVec.ofNat 64 remoteIk'.bytes.length = remoteIk'.cap := by
      rw [hrem_bytes, ← hrem_cap]
    rw [h0, h1, h2, h3]
    ac_rfl
  have hroot_hdr :
      ((sp + 0xcd0#64) ↦₆₄ 32#64) ∗ ((sp + 0xcd8#64) ↦₆₄ rootPtr') ∗
        ((sp + 0xce0#64) ↦₆₄ 32#64) ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) =
      vecU8At A (sp + 0xca0#64 + 0x30#64) 32#64 rootPtr' (keyToBytes32 x.st.rootKey) := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xca0#64 + 0x30#64 = sp + 0xcd0#64 := by bv_arith
    have h1 : sp + 0xcd0#64 + 8#64 = sp + 0xcd8#64 := by bv_arith
    have h2 : sp + 0xcd0#64 + 16#64 = sp + 0xce0#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (keyToBytes32 x.st.rootKey).length = 32#64 := by
      simp [keyToBytes32]
    rw [h0, h1, h2, h3]
    ac_rfl
  have hchains_hdr :
      ((sp + 0xce8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xcf0#64) ↦₆₄ chainsPtr') ∗
        ((sp + 0xcf8#64) ↦₆₄ chainsCap') ∗
        vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) =
      vecAt A 104 8 (chainAt A) (sp + 0xca0#64 + 0x48#64) chainsCap' chainsPtr'
        (chains'.zip x.st.receiverChains) := by
    unfold vecAt vecHeader
    have h0 : sp + 0xca0#64 + 0x48#64 = sp + 0xce8#64 := by bv_arith
    have h1 : sp + 0xce8#64 + 8#64 = sp + 0xcf0#64 := by bv_arith
    have h2 : sp + 0xce8#64 + 16#64 = sp + 0xcf8#64 := by bv_arith
    have h3 : BitVec.ofNat 64 (chains'.zip x.st.receiverChains).length = chainsCap' := by
      simp [hchains_len, hchains_cap]
    rw [h0, h1, h2, h3]
    ac_rfl
  have halice_hdr :
      ((sp + 0xd00#64) ↦₆₄ alice'.cap) ∗ ((sp + 0xd08#64) ↦₆₄ alice'.ptr) ∗
        ((sp + 0xd10#64) ↦₆₄ alice'.cap) ∗
        vecU8Buf A alice'.cap alice'.ptr alice'.bytes =
      vecGhostAt A alice' (sp + 0xca0#64 + 0x60#64) := by
    unfold vecGhostAt
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xca0#64 + 0x60#64 = sp + 0xd00#64 := by bv_arith
    have h1 : sp + 0xd00#64 + 8#64 = sp + 0xd08#64 := by bv_arith
    have h2 : sp + 0xd00#64 + 16#64 = sp + 0xd10#64 := by bv_arith
    have h3 : BitVec.ofNat 64 alice'.bytes.length = alice'.cap := by
      rw [halice_bytes, ← halice_cap]
    rw [h0, h1, h2, h3]
    ac_rfl
  have hpq_hdr :
      ((sp + 0xd18#64) ↦₆₄ pqCap') ∗ ((sp + 0xd20#64) ↦₆₄ pqPtr') ∗
        ((sp + 0xd28#64) ↦₆₄ pqCap') ∗
        vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState =
      vecU8At A (sp + 0xca0#64 + 0x78#64) pqCap' pqPtr' x.st.pqRatchetState := by
    rw [vecU8At_eq_header_sep_buf]
    unfold vecHeader
    have h0 : sp + 0xca0#64 + 0x78#64 = sp + 0xd18#64 := by bv_arith
    have h1 : sp + 0xd18#64 + 8#64 = sp + 0xd20#64 := by bv_arith
    have h2 : sp + 0xd18#64 + 16#64 = sp + 0xd28#64 := by bv_arith
    rw [h0, h1, h2, ← hpq_cap]
    ac_rfl
  have hsc_reasm :
      (((sp + 0xd30#64) ↦₆₄ scCap') ∗
        chunks96_6QAt (sp + 0xd38#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
        optSenderChainHeap A sender' x.st.senderChain) ⊢
      optSenderChainAt A (sp + 0xca0#64 + 0x90#64) sender' x.st.senderChain := by
    have h0 : sp + 0xca0#64 + 0x90#64 = sp + 0xd30#64 := by bv_arith
    have h8 : sp + 0xd30#64 + 0x8#64 = sp + 0xd38#64 := by bv_arith
    rw [h0, ← h8, ← sepConj_assoc, ← chunks104W6QAt_eq_word_sep_chunks96]
    exact optSenderChainAt_of_chunks104W6Q A (sp + 0xd30#64) sender' x.st.senderChain hsc_inl
  have hpend_reasm :
      (((sp + 0xd98#64) ↦₆₄ pendCap') ∗ ((sp + 0xda0#64) ↦₆₄ pendPtr') ∗
        ((sp + 0xda8#64) ↦₆₄ pendCap') ∗ ((sp + 0xdb0#64) ↦₃₂ w28) ∗
        ((sp + 0xdb4#64) ↦₃₂ w2c) ∗ ((sp + 0xdb8#64) ↦₆₄ v08) ∗
        ((sp + 0xdc0#64) ↦₃₂ w24) ∗ memRegion (sp + 0xdc4#64) 4 ∗
        OptPendClone A x.G.pending pendCap' pendPtr') ⊢
      ∃∗ pend' : Option TailVecGhost,
        ⌜pend'.isSome = x.G.pending.isSome⌝ ∗
          optTailVecAt A 48 (sp + 0xca0#64 + 0xf8#64) pend' := by
    have h0 : sp + 0xca0#64 + 0xf8#64 = sp + 0xd98#64 := by bv_arith
    have h8 : sp + 0xd98#64 + 8#64 = sp + 0xda0#64 := by bv_arith
    have h16 : sp + 0xd98#64 + 16#64 = sp + 0xda8#64 := by bv_arith
    have h24 : sp + 0xd98#64 + 24#64 = sp + 0xdb0#64 := by bv_arith
    have h28 : sp + 0xd98#64 + 28#64 = sp + 0xdb4#64 := by bv_arith
    have h32 : sp + 0xd98#64 + 32#64 = sp + 0xdb8#64 := by bv_arith
    have h40 : sp + 0xd98#64 + 40#64 = sp + 0xdc0#64 := by bv_arith
    have h44 : sp + 0xd98#64 + 44#64 = sp + 0xdc4#64 := by bv_arith
    rw [h0, ← h8, ← h16, ← h24, ← h28, ← h32, ← h40, ← h44]
    exact optTailVecAt_48_of_optPendClone A (sp + 0xd98#64) x.G.pending pendCap' pendPtr' w28 w2c v08 w24
  have hkyb_reasm :
      (((sp + 0xdc8#64) ↦₆₄ kybCap') ∗ ((sp + 0xdd0#64) ↦₆₄ kybPtr') ∗
        ((sp + 0xdd8#64) ↦₆₄ kybCap') ∗ ((sp + 0xde0#64) ↦₃₂ w14) ∗
        memRegion (sp + 0xde4#64) 4 ∗
        OptKybClone A x.G.kyber kybCap' kybPtr') ⊢
      ∃∗ kyb' : Option TailVecGhost,
        optTailVecAt A 32 (sp + 0xca0#64 + 0x128#64) kyb' := by
    have h0 : sp + 0xca0#64 + 0x128#64 = sp + 0xdc8#64 := by bv_arith
    have h8 : sp + 0xdc8#64 + 8#64 = sp + 0xdd0#64 := by bv_arith
    have h16 : sp + 0xdc8#64 + 16#64 = sp + 0xdd8#64 := by bv_arith
    have h24 : sp + 0xdc8#64 + 24#64 = sp + 0xde0#64 := by bv_arith
    have h28 : sp + 0xdc8#64 + 28#64 = sp + 0xde4#64 := by bv_arith
    rw [h0, ← h8, ← h16, ← h24, ← h28]
    exact optTailVecAt_32_of_optKybClone A (sp + 0xdc8#64) x.G.kyber kybCap' kybPtr' w14
  have htail_eq :
      ((sp + 0xde8#64) ↦₃₂ x.st.sessionVersion) ∗
        ((sp + 0xdec#64) ↦₃₂ x.st.previousCounter) ∗
        ((sp + 0xdf0#64) ↦₃₂ w288) ∗ ((sp + 0xdf4#64) ↦₃₂ w28c) =
      ((sp + 0xca0#64 + 0x148#64) ↦₃₂ x.st.sessionVersion) ∗
        ((sp + 0xca0#64 + 0x14c#64) ↦₃₂ x.st.previousCounter) ∗
        ((sp + 0xca0#64 + 0x150#64) ↦ₛ x.G.regIds) := by
    have h148 : sp + 0xca0#64 + 0x148#64 = sp + 0xde8#64 := by bv_arith
    have h14c : sp + 0xca0#64 + 0x14c#64 = sp + 0xdec#64 := by bv_arith
    have h150 : sp + 0xca0#64 + 0x150#64 = sp + 0xdf0#64 := by bv_arith
    have h154 : sp + 0xdf0#64 + 4#64 = sp + 0xdf4#64 := by bv_arith
    rw [h148, h14c, h150, h_reg_pts (sp + 0xdf0#64), h154]
  unfold segClone_dstSlotsWrittenAt
  refine Entails.trans
    (Q := (((sp + 0xd98#64) ↦₆₄ pendCap') ∗ ((sp + 0xda0#64) ↦₆₄ pendPtr') ∗
            ((sp + 0xda8#64) ↦₆₄ pendCap') ∗ ((sp + 0xdb0#64) ↦₃₂ w28) ∗
            ((sp + 0xdb4#64) ↦₃₂ w2c) ∗ ((sp + 0xdb8#64) ↦₆₄ v08) ∗
            ((sp + 0xdc0#64) ↦₃₂ w24) ∗ memRegion (sp + 0xdc4#64) 4 ∗
            OptPendClone A x.G.pending pendCap' pendPtr') ∗
          (((sp + 0xdc8#64) ↦₆₄ kybCap') ∗ ((sp + 0xdd0#64) ↦₆₄ kybPtr') ∗
            ((sp + 0xdd8#64) ↦₆₄ kybCap') ∗ ((sp + 0xde0#64) ↦₃₂ w14) ∗
            memRegion (sp + 0xde4#64) 4 ∗
            OptKybClone A x.G.kyber kybCap' kybPtr') ∗
          (((sp + 0xd30#64) ↦₆₄ scCap') ∗
            chunks96_6QAt (sp + 0xd38#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            optSenderChainHeap A sender' x.st.senderChain) ∗
          (((sp + 0xca0#64) ↦₆₄ localIk'.cap) ∗ ((sp + 0xca8#64) ↦₆₄ localIk'.ptr) ∗
            ((sp + 0xcb0#64) ↦₆₄ localIk'.cap) ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes) ∗
          (((sp + 0xcb8#64) ↦₆₄ remoteIk'.cap) ∗ ((sp + 0xcc0#64) ↦₆₄ remoteIk'.ptr) ∗
            ((sp + 0xcc8#64) ↦₆₄ remoteIk'.cap) ∗
            vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes) ∗
          (((sp + 0xcd0#64) ↦₆₄ 32#64) ∗ ((sp + 0xcd8#64) ↦₆₄ rootPtr') ∗
            ((sp + 0xce0#64) ↦₆₄ 32#64) ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey)) ∗
          (((sp + 0xce8#64) ↦₆₄ chainsCap') ∗ ((sp + 0xcf0#64) ↦₆₄ chainsPtr') ∗
            ((sp + 0xcf8#64) ↦₆₄ chainsCap') ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains)) ∗
          (((sp + 0xd00#64) ↦₆₄ alice'.cap) ∗ ((sp + 0xd08#64) ↦₆₄ alice'.ptr) ∗
            ((sp + 0xd10#64) ↦₆₄ alice'.cap) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes) ∗
          (((sp + 0xd18#64) ↦₆₄ pqCap') ∗ ((sp + 0xd20#64) ↦₆₄ pqPtr') ∗
            ((sp + 0xd28#64) ↦₆₄ pqCap') ∗
            vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState) ∗
          (((sp + 0xde8#64) ↦₃₂ x.st.sessionVersion) ∗
            ((sp + 0xdec#64) ↦₃₂ x.st.previousCounter) ∗
            ((sp + 0xdf0#64) ↦₃₂ w288) ∗ ((sp + 0xdf4#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hloc_hdr, hrem_hdr, hroot_hdr, hchains_hdr, halice_hdr, hpq_hdr, htail_eq]
  refine Entails.trans
    (sepConj_mono hpend_reasm (sepConj_mono hkyb_reasm (sepConj_mono_left hsc_reasm))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro kyb'
  apply Entails.sepExists_elim; intro pend'
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hpend'_some
  let G₁ : SessionGhost :=
    { localIk := localIk'
      remoteIk := remoteIk'
      root := ⟨32#64, rootPtr'⟩
      chainsCap := chainsCap'
      chainsPtr := chainsPtr'
      chains := chains'
      alice := alice'
      pq := ⟨pqCap', pqPtr'⟩
      sender := sender'
      pending := pend'
      kyber := kyb'
      regIds := x.G.regIds }
  refine Entails.sepExists_right G₁ ?_
  have hclone : CloneRel x.G G₁ := ⟨hloc_bytes, hrem_bytes, halice_bytes, rfl⟩
  apply Entails.pure_right hclone
  unfold sessionStateAt
  have hpure :
      PublicKey.deserialize G₁.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
      (match x.st.remoteIdentity with
       | none => G₁.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G₁.remoteIk.bytes = .ok ik.publicKey) ∧
      G₁.chains.length = x.st.receiverChains.length ∧
      G₁.pending.isSome = x.st.pendingPreKey ∧ G₁.regIds.length = 8 ∧
      G₁.localIk.bytes.length = 33 ∧
      (x.st.remoteIdentity.isSome → G₁.remoteIk.bytes.length = 33) := by
    dsimp [G₁]
    rw [hloc_bytes, hrem_bytes, hpend'_some]
    exact ⟨h_loc_deser, h_rem_deser, hchains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩
  apply Entails.pure_right hpure
  dsimp only [G₁]
  exact Entails.of_eq (by ac_rfl)

theorem segClone_chunks96_6QAt_sp_0xd38 (sp : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) :
    chunks96_6QAt (sp + 0xd38#64) q0 q1 q2 q3 q4 q5 =
      ((sp + 0xd38#64) ↦₁₂₈ q0) ∗ ((sp + 0xd48#64) ↦₁₂₈ q1) ∗
      ((sp + 0xd58#64) ↦₁₂₈ q2) ∗ ((sp + 0xd68#64) ↦₁₂₈ q3) ∗
      ((sp + 0xd78#64) ↦₁₂₈ q4) ∗ ((sp + 0xd88#64) ↦₁₂₈ q5) := by
  unfold chunks96_6QAt
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

def segClone_clonePost (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧
    sf.readReg64 .x29 = s0.readReg64 .x29 ∧ sf.trace = s0.trace ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost,
      ⌜CloneRel x.G G₁⌝ ∗
      recFrame A img x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗
      sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗
      memRegion (s0.sp + 0x4b0#64) 48 ∗
      tapeAt ctl x.cur x.rest)

structure SpillVals where
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

theorem memRegion_0x80_entails_spillSlotsAt (sp : BitVec 64) :
    memRegion sp 0x80 ⊢
      ∃∗ sv : SpillVals,
        spillSlotsAt sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c sv.v30
          sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 :=
  memRegion_0x80_entails_spillSlotsAt_gen sp SpillVals.mk
    (fun sv => spillSlotsAt sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c sv.v30
      sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

structure DstVals where
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

def dstSlotsAt (sp : BitVec 64) (dv : DstVals) : SepProp :=
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

theorem memRegion_344_entails_dstSlotsAt (sp : BitVec 64) :
    memRegion (sp + 0xca0#64) 344 ⊢ ∃∗ dv : DstVals, dstSlotsAt sp dv :=
  memRegion_344_entails_dstSlotsAt_gen sp DstVals.mk (dstSlotsAt sp)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

def segClone_dstSlotsMidAt (sp : BitVec 64) (dv : DstVals)
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

end CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
