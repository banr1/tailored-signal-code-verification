/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Responder Closure 4K-Stack Extern Stubs & `finish_grow`

Proves `decryptPrekeyClosure_{alloc,dealloc,shim,memcpy}_ok_ext{_4k}`,
`decryptPrekeyClosure_panic_at_handle_error_ext`, and `finish_grow_ok_ext_4k` on
`tripleRatchetProgAtExt b ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.InImageLift
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

abbrev closureAllocRelOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)

abbrev closureDeallocRelOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)

abbrev closureShimRelOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)

abbrev closureMemcpyRelOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "memcpy" -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)

abbrev closureHandleErrorRelOff : BitVec 64 :=
  bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
    (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)

theorem decryptPrekeyClosure_alloc_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureAllocRelOff)
      (rustAllocSpec A) :=
  hA.alloc_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_alloc" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
    (by simp only [arm64_norm])

theorem decryptPrekeyClosure_alloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureAllocRelOff)
      (rustAllocSpec A) :=
  decryptPrekeyClosure_alloc_ok_ext_4k (AllocContractsMem4K.of_AllocContracts hA)

theorem decryptPrekeyClosure_dealloc_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureDeallocRelOff)
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
    (by simp only [arm64_norm])

theorem decryptPrekeyClosure_dealloc_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureDeallocRelOff)
      (rustDeallocSpec A) :=
  decryptPrekeyClosure_dealloc_ok_ext_4k (AllocContractsMem4K.of_AllocContracts hA)

theorem decryptPrekeyClosure_shim_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureShimRelOff)
      sessionShimSpec :=
  hA.shim_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
    (by simp only [arm64_norm])

theorem decryptPrekeyClosure_shim_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureShimRelOff)
      sessionShimSpec :=
  decryptPrekeyClosure_shim_ok_ext_4k (AllocContractsMem4K.of_AllocContracts hA)

theorem decryptPrekeyClosure_memcpy_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureMemcpyRelOff)
      (sessionMemcpySpec allocHookStack) :=
  hA.session_memcpy_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "memcpy" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
    (by simp only [arm64_norm])

theorem decryptPrekeyClosure_memcpy_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureMemcpyRelOff)
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "memcpy" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))

theorem decryptPrekeyClosure_panic_at_handle_error_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureHandleErrorRelOff) =
      some Rust.panicked :=
  panic_at_handle_error_ext b ext decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "alloc::raw_vec::handle_error" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` meets `finishGrowSpec A` on
`tripleRatchetProgAtExt b ext` under `AllocContractsMem4K b A ext` (`allocHookStack = 4096`). -/
theorem finish_grow_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) := by
  apply subroutine_ok_of_optNone
  refine finish_grow_ok_of_hooks_opt (by decide) ?_ ?_ ?_
  · apply subroutine_ok_to_optNone
    have h := subroutine_ok_withStack_of_subroutine_ok
      (hA.shim_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
      allocHookStack
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
      dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout
  · exact subroutine_ok_to_optNone
      (hA.alloc_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
  · exact subroutine_ok_to_optNone
      (rustReallocExternWithStack_of_rustRealloc
        (hA.realloc_ok_at finishGrowName
          (num% (ls_off% "__rustc::__rust_realloc" -
            ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
        (by decide) (by decide))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
