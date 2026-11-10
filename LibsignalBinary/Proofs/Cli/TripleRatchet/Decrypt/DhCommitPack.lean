/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitChain
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# `try_decrypt_with_state` S3 Commit Address and Layout Helpers

Callee/hook address equalities and byte/word memory-splitting helpers for the S3 commit sub-segment.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt

open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Byte/Word Packing and Layout Splitting Helpers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.tryDecryptEntry_eq_base {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry entryOf
  rw [libsignalSessionCode_ofImage h, Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_tryDecrypt_eq_base (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName = b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.tryDecryptEntry_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptEntry img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.tryDecryptEntry_eq_base h, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_tryDecrypt_eq_base]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.segS3CommitPC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.segDhCommitPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0x8ac#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.segDhCommitPC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.tryDecryptEntry_eq_fnAddr h ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.segS4PC_eq_fnAddr {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC img = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + 0x3e4#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.segConsumeMsgKeyPC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.tryDecryptEntry_eq_fnAddr h ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_publicKeySerialize_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_chainKeyToPb_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_growOneChain_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr growOneChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.fnAddr_dropChain_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.Getters.dropChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#2]")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.shim_ok_at_0xe6a8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) noAllocShimSpec :=
  hA.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.alloc_ok_at_0xe6ac {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustAllocSpec A) :=
  hA.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.dealloc_ok_at_0xe6b8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (rustDeallocSpec A) :=
  hA.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.memmove_ok_at_0xe6c0 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (stackSize : Nat := 4096) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "memmove" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) (sessionMemmoveSpec stackSize) :=
  hA.session_memmove_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "memmove" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>")) stackSize

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.memcpy_ok_at_0xe6d8 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) framelessMemcpySpec :=
  hA.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "memcpy" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.panic_at_0xe6f4 {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>") % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptName (num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_ratchet::Coins>"))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.satisfies_tryDecrypt_onPanic_of_allocFailed
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image) (x : TryDecryptGhost)
    {s0 sf : State} {P R : SepProp}
    (hfail : allocFailedIn s0 sf) (hpfx : s0.trace <+: sf.trace)
    (hmem : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R := by
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨Or.inr (Or.inr hfail), hpfx⟩, ?_⟩
  exact Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap P)) hmem

def _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic (prog : Program) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image)
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State) (Post : State → Prop) : Prop :=
  ∃ s', Steps prog s s' ∧
    (Post s' ∨
     (s'.status = .Panicked ∧
       (s'.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R)))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.done {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {Post : State → Prop}
    (h : Post s) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Post :=
  ⟨s, .refl s, Or.inl h⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.seq {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State} {P Q : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s P)
    (h2 : ∀ s1, s.mem.KeepsFrozen s1.mem → s1.symtab = s.symtab → P s1 →
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hP | hPan⟩ := h1
  · obtain ⟨s2, hsteps2, hQ⟩ := h2 s1 hsteps1.keepsFrozen hsteps1.symtab_eq hP
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact ⟨s1, hsteps1, Or.inr hPan⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_sepWP {prog : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
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
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hpost1⟩ | ⟨_, hoom⟩⟩ := hwp.elim hmem hL
  · have hkf1 := hsteps1.keepsFrozen
    have hsym1 := hsteps1.symtab_eq
    have hL1 := hL.of_keepsFrozen hkf1
    obtain ⟨s2, hsteps2, hQ⟩ := hcont s1 P_out hpc1 hrun1 hkf1 hsym1 hL1 hm1 hpost1
    exact ⟨s2, hsteps1.trans hsteps2, hQ⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_no_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
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
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
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

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_call_alloc_panic {α : Type} {prog : Program} {C : Crypto} {A : RustAlloc}
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
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s1 Q)
    (hoom_false : ∀ sf, spec.onOom arg s sf = ⌜False⌝ := by intro _; rfl) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  obtain ⟨s1, hsteps1, hout, -⟩ :=
    hcall.no_fault_before_outcome arg (Frame ∗ R) s hpc hrun hpre hsp hL
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
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail0 hpfx0 hmem1⟩⟩
  · rw [hexit_false code s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1
  · rw [hoom_false s1, satisfies_pure_sepConj] at hpost1
    exact False.elim hpost1.1

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic.of_panic_extern {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {P R : SepProp} {s0 s : State} {Q : State → Prop}
    (hrun : s.status = .Running)
    (hext : prog.externAt? s.pc = some Rust.panicked)
    (hfail : allocFailedIn s0 s) (hpfx : s0.trace <+: s.trace)
    (hmem : s.mem ⊨ P ∗ R) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.ReachesOrPanic prog C A ctl uuidTryParse S img x R s0 s Q := by
  refine ⟨Rust.panicked s,
    Steps.step (Step.extern hrun hext (Memory.KeepsFrozen.refl _)) (Steps.refl _),
    Or.inr ⟨rfl, ?_⟩⟩
  have hfail' : allocFailedIn s0 (Rust.panicked s) := hfail
  have hpfx' : s0.trace <+: (Rust.panicked s).trace := hpfx
  have hmem' : (Rust.panicked s).mem ⊨ P ∗ R := hmem
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.satisfies_tryDecrypt_onPanic_of_allocFailed C A ctl S img x hfail' hpfx' hmem'

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhCommit
