/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHChain
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegDhHPack
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhHChain
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# DH Commit Packing, `fnAddr` Rewriting, and Extern Hook Helpers (`ext` & `trap`)

Byte/word packing, stack layout splitting, `fnAddr` normalization, and extern hook lemmas on
`tripleRatchetProgAtExt` (`AllocContractsMem4K`) with `trTrapProgAt` specializations.
-/

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

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_split_bottom_pack_ext (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 n) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  · bv_arith
  · rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
      BitVec.sub_add_cancel]

/-! ## Byte/Word Packing, `fnAddr` Rewriting, and Extern Hook Helpers (`ext` & `trap`) -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName =
      b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr_ext
    {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_base h,
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base_ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC_eq_fnAddr_ext
    {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8ac#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr_ext h ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS4PC_eq_fnAddr_ext
    {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x3e4#64 := by
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr_ext h ext]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_publicKeySerialize_eq_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    libsignalSessionCode_fnOff_0x3e2c4]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_chainKeyToPb_eq_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt b ext).fnAddr chainKeyToPbName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    libsignalSessionCode_fnOff_0xcf68]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_growOneChain_eq_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt b ext).fnAddr growOneChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    libsignalSessionCode_fnOff_0x15cac]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_dropChain_eq_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.shim_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      sessionShimSpec := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          bv% ((2 ^ 64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
        (tripleRatchetProgAtExt b ext).fnAddr shimName := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]
    bv_omega
  rw [haddr]
  exact hA.shim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.noAllocShim_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      noAllocShimSpec := by
  have h := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.shim_ok_at_ext hA
  refine subroutine_ok_outcome_intro fun u R s0 hpc hrun hpre hal => ?_
  refine h.mono_outcome u R s0 hpc hrun (by simpa only [sessionShimSpec, noAllocShimSpec] using hpre) hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simpa only [sessionShimSpec, noAllocShimSpec] using hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.alloc_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_alloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      (rustAllocSpec A) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          bv% ((2 ^ 64 + ls_off% "__rustc::__rust_alloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
        (tripleRatchetProgAtExt b ext).fnAddr allocName := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_stub% "__rustc::__rust_alloc")]
    bv_omega
  rw [haddr]
  exact hA.alloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.dealloc_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      (rustDeallocSpec A) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
        (tripleRatchetProgAtExt b ext).fnAddr deallocName := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_stub% "__rustc::__rust_dealloc")]
    bv_omega
  rw [haddr]
  exact hA.dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memmove_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext)
    (stackSize : Nat := 4096)
    (hstk : allocHookStack ≤ stackSize := by decide)
    (hstk' : stackSize ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "memmove" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      (sessionMemmoveSpec stackSize) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          bv% ((2 ^ 64 + ls_off% "memmove" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
        (tripleRatchetProgAtExt b ext).fnAddr memmoveName := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_stub% "memmove")]
    bv_omega
  rw [haddr]
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stackSize =
      stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have heq : stackSize = allocHookStack + (stackSize - allocHookStack) := by omega
    conv_lhs => rw [heq]
    exact stackAt_split_bottom_pack_ext s0.sp allocHookStack (stackSize - allocHookStack) (by omega)
  have hpre' : s0.mem ⊨ (sessionMemmoveSpec allocHookStack).pre x s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗ R) := by
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec] at hpre ⊢
    rw [hsplit] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  refine hA.session_memmove.mono_outcome x
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗ R)
    s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemmoveSpec, libcMemmoveSpec] at hpost ⊢
    rw [hsplit]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memcpy_ok_at_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext)
    (stackSize : Nat := 4096)
    (hstk : allocHookStack ≤ stackSize := by decide)
    (hstk' : stackSize ≤ 2 ^ 64 := by decide) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "memcpy" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64))
      (sessionMemcpySpec stackSize) := by
  have haddr :
      (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
          bv% ((2 ^ 64 + ls_off% "memcpy" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
        (tripleRatchetProgAtExt b ext).fnAddr memcpyName := by
    unfold tripleRatchetProgAtExt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_stub% "memcpy")]
    bv_omega
  rw [haddr]
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp stackSize =
      stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗
        stackAt s0.sp allocHookStack := by
    have heq : stackSize = allocHookStack + (stackSize - allocHookStack) := by omega
    conv_lhs => rw [heq]
    exact stackAt_split_bottom_pack_ext s0.sp allocHookStack (stackSize - allocHookStack) (by omega)
  have hpre' : s0.mem ⊨ (sessionMemcpySpec allocHookStack).pre x s0 ∗
      (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗ R) := by
    dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpre ⊢
    rw [hsplit] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre
  refine hA.session_memcpy.mono_outcome x
    (stackAt (s0.sp - BitVec.ofNat 64 allocHookStack) (stackSize - allocHookStack) ∗ R)
    s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionMemcpySpec, libcMemcpySpec] at hpost ⊢
    rw [hsplit]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.panic_at_handle_error_ext
    {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        bv% ((2 ^ 64 + ls_off% "alloc::raw_vec::handle_error" -
          ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64)) =
      some Rust.panicked :=
  panic_at_panicSymbol
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    rfl (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by simp [Rust.isPanicSymbol])

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName = b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_tryDecrypt_eq_base_ext b (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr_trap {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.tryDecryptEntry_eq_fnAddr_ext h (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC_eq_fnAddr_trap {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC img =
      (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x8ac#64 :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS3CommitPC_eq_fnAddr_ext h (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS4PC_eq_fnAddr_trap {img : Obj.Image} (h : Obj.Loads libsignalSessionImage img)
    (C : Crypto)
    (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS4PC img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + 0x3e4#64 :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.segS4PC_eq_fnAddr_ext h (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_publicKeySerialize_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (trTrapProgAt b C abs).fnAddr publicKeySerializeName :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_publicKeySerialize_eq_ext b (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_chainKeyToPb_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<libsignal_protocol::ratchet::keys::ChainKey>::to_pb" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (trTrapProgAt b C abs).fnAddr chainKeyToPbName :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_chainKeyToPb_eq_ext b (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_growOneChain_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (trTrapProgAt b C abs).fnAddr growOneChainName :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_growOneChain_eq_ext b (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_dropChain_eq_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::session_structure::Chain> [local#3]" - ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2^64) =
      (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.dropChainName :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.fnAddr_dropChain_eq_ext b (trTrapExterns C abs)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.shim_ok_at_0xe6a8_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) noAllocShimSpec :=
  hook_ok_at (k :=
    num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by simp [Rust.isPanicSymbol])
    ⟨hookNoop, rfl, noAllocShim_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.alloc_ok_at_0xe6ac_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustAllocSpec A) :=
  hook_ok_at_raw (k :=
    num% (ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by
    decide)
    (ls_hook% "__rustc::__rust_alloc")
    (CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.allocHooks_tripleRatchetExterns_trap C A abs hA).alloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.dealloc_ok_at_0xe6b8_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) (rustDeallocSpec A) :=
  hook_ok_at_raw (k :=
    num% (ls_off% "__rustc::__rust_dealloc" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by
    decide)
    (ls_hook% "__rustc::__rust_dealloc")
    (CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.allocHooks_tripleRatchetExterns_trap C A abs hA).dealloc

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memmove_ok_at_0xe6c0_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (stackSize : Nat := 4096) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "memmove" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
        (sessionMemmoveSpec stackSize) :=
  hook_ok_at (k :=
    num% (ls_off% "memmove" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "memmove") (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookSessionMemmove_ok (hookStack := stackSize)⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.memcpy_ok_at_0xe6d8_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64))
        framelessMemcpySpec :=
  hook_ok_at (k :=
    num% (ls_off% "memcpy" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") rfl (by decide)
    (ls_hook% "memcpy") (by simp [Rust.isPanicSymbol])
    ⟨hookMemcpy, rfl, framelessMemcpy_hookOk⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.panic_at_0xe6f4_trap {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)} :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + bv% ((2^64 + ls_off%
        "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) % 2^64)) =
      some Rust.panicked :=
  CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegBH.panic_at_handle_error_ext

end CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegBH
