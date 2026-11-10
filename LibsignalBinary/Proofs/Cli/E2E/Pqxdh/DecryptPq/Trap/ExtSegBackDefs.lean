/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Stage2ContractsExt
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegBackDefs
import LibsignalBinary.Proofs.FnOffEq

/-!
# Contract-Backed (`Stage2ContractsExt` / `AllocContractsMem4K`) Back-Segment Helpers (`SegBackDefs`)

Entry / PC rewriting, backward `BL` targets, extern hook `subroutine_ok` wrappers, panic bridge,
and stack-budget transition helpers for handshake `try_decrypt_with_state::<Coins>` (`S7`, `S8`, `S9`)
directly on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (LayoutOk RustAlloc allocFailedEvent allocFailedIn rustAllocSpec
  rustDeallocSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel Stage2ContractsWeak TrGhost TryDecryptGhost
  aesDecSpec entryOf_eq_tripleRatchetProgAtExt extHookStack formatInnerSpec
  panic_at_handle_error_ext rootStack rustAllocSpecWithStack rustDeallocExternSpecWithStack
  sessionMemcpyRegionSpec sessionShimSpec trApplyName trApplyStackX tripleRatchetProgAtExt
  verifyMacWithAddressesName withStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (clearUpkName clearUpkStackX)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq (tryDecryptFrameSize tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD (stackAt_sub_split)
open CryptoVerification.SignalSession.Cli.Slots (Stage2ContractsExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (AllocContractsMem4K)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackDefs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero

/-- Fetch hypotheses for handshake `try_decrypt_with_state::<Coins>` on `tripleRatchetProgAtExt b ext`,
from fn-relative offset `k0`, `len` bytes. -/
macro "decrypt_fetches_ext_cli_pq " b:term:max ext:term:max
    hfn:term:max k0:num len:num : tactic =>
  `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalTripleRatchetBinCli $b
    (Rust.withPanics $ext) $hfn
    (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")
    $k0 $len)

/-! ## 1. Entry / PC Rewriting and Backward `BL` Targets on `tripleRatchetProgAtExt` -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName :=
  entryOf_eq_tripleRatchetProgAtExt ext himg
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS7PC_eq_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x63c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS7PC,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS8PC_eq_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x678 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS8PC,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.segS9PC_eq_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x6a4 := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS9PC,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.errTailPC_eq_ext
    {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (ext : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC img =
      (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName + BitVec.ofNat 64 0x30c := by
  rw [CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.errTailPC,
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecryptEntry_eq_fnAddr_ext himg]

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_verifyMac_target_ext
    (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_trApply_target_ext
    (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt img.base ext).fnAddr trApplyName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::TripleRatchet>::apply_to_session_state")]
  bv_omega

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.bl_clearUpk_target_ext
    (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
      bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message" -
        ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>") % 2 ^ 64) =
      (tripleRatchetProgAtExt img.base ext).fnAddr clearUpkName := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"),
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message")]
  bv_omega

/-! ## 2. Hook / Callee Wrappers under `Stage2ContractsExt`, `Stage2ContractsWeak` & `AllocContractsMem4K` -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.shim_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hW : Stage2ContractsWeak img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((withStack sessionShimSpec extHookStack).inImage img) :=
  hW.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.memcpy_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hW : Stage2ContractsWeak img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "memcpy" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((withStack sessionMemcpyRegionSpec extHookStack).inImage img) :=
  hW.session_memcpy_region_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "memcpy" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.alloc_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hW : Stage2ContractsWeak img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_alloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((rustAllocSpecWithStack A extHookStack).inImage img) :=
  hW.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hW : Stage2ContractsWeak img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  hW.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.formatInner_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hW : Stage2ContractsWeak img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "alloc::fmt::format::format_inner" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((formatInnerSpec A).inImage img) :=
  hW.format_inner_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "alloc::fmt::format::format_inner" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.aesDec_ok_at_ext
    (img : Obj.Image) {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsExt img C A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      ((aesDecSpec C.D A).inImage img) :=
  hC.aes_dec_exact_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "signal_crypto::aes_cbc::aes_256_cbc_decrypt" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.shim_ok_at_mem4k
    (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hM : AllocContractsMem4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      sessionShimSpec :=
  hM.shim_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.alloc_ok_at_mem4k
    (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hM : AllocContractsMem4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_alloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      (rustAllocSpec A) :=
  hM.alloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.dealloc_ok_at_mem4k
    (img : Obj.Image) {A : RustAlloc} {ext : String → Option (State → State)}
    (hM : AllocContractsMem4K img.base A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")))
      (rustDeallocSpec A) :=
  hM.dealloc_ok_at CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.externAt_handle_error_ext
    (img : Obj.Image) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt img.base ext).externAt?
      ((tripleRatchetProgAtExt img.base ext).fnAddr
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName +
        BitVec.ofNat 64 (num%
          (ls_off% "alloc::raw_vec::handle_error" -
            ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))) =
      some Rust.panicked :=
  panic_at_handle_error_ext img.base ext
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName
    (num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>"))
    (hk := by fnoff_eq)

/-! ## 3. `SepWPp` Panic Bridge & Stack-Budget Transition Helpers -/

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.panic_direct_ext
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (img : Obj.Image)
    (ext : String → Option (State → State))
    (x : TryDecryptGhost) (s0 s : State) (ret panic_pc : BitVec 64)
    (P R : SepProp) {Q : State → SepProp → Prop}
    (hpc : s.pc = panic_pc) (hrun : s.status = .Running)
    (hext : (tripleRatchetProgAtExt img.base ext).externAt? panic_pc = some Rust.panicked)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => sf.status = .Panicked → (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R)) := by
  refine CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegD.SepWPp.panic_at hpc hrun hext fun _ hm_pan => ?_
  have htr_f : (Rust.panicked s).trace = s0.trace ++ [allocFailedEvent] := htr
  have haf : allocFailedIn s0 (Rust.panicked s) := by
    unfold allocFailedIn
    rw [htr_f, List.drop_left]
    exact List.Mem.head _
  have hpre : s0.trace <+: (Rust.panicked s).trace := by
    rw [htr_f]
    exact ⟨[allocFailedEvent], rfl⟩
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.tryDecrypt_onPanic_of_direct
    C A ctl S img x s0 (Rust.panicked s) P R haf hpre hm_pan

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.layoutOk_of_cap_ne_zero
    {cap : BitVec 64} (hcap : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 :=
  ⟨by bv_omega, ⟨0, rfl⟩, by omega⟩

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.stackAt_sub_to_ext
    (sp : BitVec 64) {n : Nat} (hlo : extHookStack ≤ n) (hhi : n ≤ tryDecryptSubStack) :
    memRegion (sp - 262144#64) (tryDecryptSubStack - n) ∗ stackAt (sp - 1504#64) n ⊢
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ∗
      stackAt (sp - 1504#64) extHookStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) n hhi
  have h2 := stackAt_sub_split (sp - 1504#64) extHookStack (Nat.le_trans hlo hhi)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [← h1, h2]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.extHookStack_to_trApplyStackX
    (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) := by
  have h1 := stackAt_sub_split (sp - 1504#64) extHookStack (by decide)
  have h2 := stackAt_sub_split (sp - 1504#64) trApplyStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [sepConj_comm, ← h1, h2, sepConj_comm]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.trApplyStackX_to_clearUpkStackX
    (sp : BitVec 64) :
    stackAt (sp - 1504#64) trApplyStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - trApplyStackX) ⊢
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) := by
  have h1 := stackAt_sub_split (sp - 1504#64) trApplyStackX (by decide)
  have h2 := stackAt_sub_split (sp - 1504#64) clearUpkStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1 h2
  rw [sepConj_comm, ← h1, h2, sepConj_comm]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.clearUpkStackX_to_subStack
    (sp : BitVec 64) :
    stackAt (sp - 1504#64) clearUpkStackX ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - clearUpkStackX) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) clearUpkStackX (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegD.extHookStack_to_subStack
    (sp : BitVec 64) :
    stackAt (sp - 1504#64) extHookStack ∗
    memRegion (sp - 262144#64) (tryDecryptSubStack - extHookStack) ⊢
    stackAt (sp - 1504#64) tryDecryptSubStack := by
  have h1 := stackAt_sub_split (sp - 1504#64) extHookStack (by decide)
  rw [show sp - 1504#64 - BitVec.ofNat 64 tryDecryptSubStack = sp - 262144#64 by
        dsimp only [tryDecryptSubStack, rootStack, tryDecryptFrameSize]; bv_omega] at h1
  rw [sepConj_comm, ← h1]
  exact Entails.refl _

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegBackDefs
