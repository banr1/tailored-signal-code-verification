/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import ProofLib.SepLogic.WPp

/-!
# Handshake `DecryptPq` DH Commit Packing & Hook Helpers

Byte/word packing, stack layout splitting, `fnAddr` normalization, and extern hook lemmas for
`try_decrypt_with_state::<signal_session_handshake::Coins>` on `tripleRatchetProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.DecryptPq

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Byte/Word Packing and Layout Splitting Helpers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_base {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = img.base + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry entryOf
  rw [libsignalSessionCode_ofImage h, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_base h, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC img =
      (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8ac#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr h C ctl abs]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS4PC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x3e4#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr h C ctl abs]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_publicKeySerialize_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr publicKeySerializeName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0x3e2c4]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_chainKeyToPb_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainKeyToPbName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0xcf68]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_growOneChain_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr growOneChainName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), libsignalSessionCode_fnOff_0x15cac]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_dropChain_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName := by
  unfold tripleRatchetProgAt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.shim_ok_at_0xe6a8 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) noAllocShimSpec :=
  hook_ok_at (k :=
    num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, noAllocShim_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.alloc_ok_at_0xe6ac {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustAllocSpec A) :=
  hook_ok_at_raw (k :=
    num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by
    decide)
    (ls_hook% "__rustc::__rust_alloc")
    (allocHooks_tripleRatchetExterns C ctl A abs hA).alloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.dealloc_ok_at_0xe6b8 {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustDeallocSpec A) :=
  hook_ok_at_raw (k :=
    num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by
    decide)
    (ls_hook% "__rustc::__rust_dealloc")
    (allocHooks_tripleRatchetExterns C ctl A abs hA).dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memmove_ok_at_0xe6c0 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (stackSize : Nat := 4096) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "memmove" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
        (sessionMemmoveSpec stackSize) :=
  hook_ok_at (k :=
    num% (ls_off% "memmove" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "memmove") (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookSessionMemmove_ok (hookStack := stackSize)⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memcpy_ok_at_0xe6d8 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
        framelessMemcpySpec :=
  hook_ok_at (k :=
    num% (ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.panic_at_0xe6f4 {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) =
      some Rust.panicked :=
  panic_at_panicSymbol (k :=
    num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    rfl (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.satisfies_tryDecrypt_onPanic_of_allocFailed
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image) (x : TryDecryptGhost)
    {s0 sf : State} {P R : SepProp}
    (hfail : allocFailedIn s0 sf) (hpfx : s0.trace <+: sf.trace)
    (hmem : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hfail), hpfx⟩, ?_⟩
  have hany : P ⊢ anyHeap := ProofLib.entails_anyHeap P
  exact Satisfies.mono (sepConj_mono_left hany) hmem

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic (prog : Program) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) (Post : State → Prop) : Prop :=
  ∃ s', Steps prog s s' ∧
    (Post s' ∨
     (s'.status = .Panicked ∧
       (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.done {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {Post : State → Prop}
    (h : Post s) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Post :=
  ⟨s, .refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.seq {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → P s1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hsteps1.symtab_eq hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr hPan⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_sepWP {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {target : BitVec 64} {Pre Frame : SepProp}
    {PostWP : State → SepProp → Prop} {Q : State → Prop}
    (hwp : SepWP prog target s Pre PostWP)
    (hmem : s.mem ⊨ Pre ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hcont : ∀ s1 P_out,
      s1.pc = target → s1.status = .Running →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ P_out ∗ (Frame ∗ R)) →
      PostWP s1 P_out →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hkf1 := hsteps1.keepsFrozen
  have hsym1 := hsteps1.symtab_eq
  have hL1 := hL.of_keepsFrozen hkf1
  obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
  exact ⟨s2, hsteps1.trans hsteps2, hQ⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_call_no_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_false : ∀ sf, spec.onPanic arg s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨_, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsym1 hL1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_call_alloc_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    {entry ret_pc : BitVec 64} {spec : Spec α} {arg : α} {Frame : SepProp}
    {Q : State → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 .x30 = ret_pc)
    (htrace : s.trace = s0.trace)
    (hpre : s.mem ⊨ spec.pre arg s ∗ (Frame ∗ R))
    (hL : prog.CodeLoaded s.mem)
    (hpan_eq : ∀ sf, spec.onPanic arg s sf =
      ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit arg code s sf = ⌜False⌝ := by intros; rfl)
    (hcont : ∀ s1,
      s1.pc = ret_pc → s1.status = .Running →
      s1.sp = s.sp → s1.spAligned = true →
      CalleeSavedPreserved s s1 →
      s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab →
      prog.CodeLoaded s1.mem →
      (s1.mem ⊨ spec.post arg s s1 ∗ (Frame ∗ R)) →
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    subroutine_ok.no_fault_before_outcome hcall arg (Frame ∗ R) s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpc1, hsp1, hrun1⟩, ⟨_, hcs1⟩, hpost1⟩ | ⟨hpan1, hpost1⟩ | ⟨code, _, hpost1⟩ | ⟨_, hpost1⟩
  · rw [show Reg.lr = Reg.x30 from rfl, hlr] at hpc1
    have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    have hsp_align1 : s1.spAligned = true := by
      unfold State.spAligned at hsp ⊢; rw [hsp1]; exact hsp
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 hpc1 hrun1 hsp1 hsp_align1 hcs1 hkf1 hsym1 hL1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · rw [hpan_eq s1, sepConj_assoc, satisfies_pure_sepConj] at hpost1
    rcases hpost1 with ⟨⟨hfail, hpfx⟩, hmem1⟩
    have hfail0 : allocFailedIn s0 s1 := by
      unfold allocFailedIn at hfail ⊢; rwa [← htrace]
    have hpfx0 : s0.trace <+: s1.trace := by rwa [← htrace]
    rw [← sepConj_assoc] at hmem1
    exact ⟨s1, hsteps1, Or.inr ⟨hpan1,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail0 hpfx0 hmem1⟩⟩
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic.of_panic_extern {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {P R : SepProp} {s0 s : State} {Q : State → Prop}
    (hrun : s.status = .Running)
    (hext : prog.externAt? s.pc = some Rust.panicked)
    (hfail : allocFailedIn s0 s) (hpfx : s0.trace <+: s.trace)
    (hmem : s.mem ⊨ P ∗ R) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  refine ⟨Rust.panicked s,
    Steps.step (Step.extern hrun hext (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr ⟨rfl, ?_⟩⟩
  have hfail' : allocFailedIn s0 (Rust.panicked s) := hfail
  have hpfx' : s0.trace <+: (Rust.panicked s).trace := hpfx
  have hmem' : (Rust.panicked s).mem ⊨ P ∗ R := hmem
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail' hpfx' hmem'

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
