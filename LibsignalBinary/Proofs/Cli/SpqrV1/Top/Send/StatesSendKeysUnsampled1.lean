/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.SignalSession.Coins.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtSegDhDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SignalSession.Coins.Fill
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Inlined `States::send` `.keysUnsampled` Sub-Steps (`+372..+684`) for CLI `spqr::send`

Proves `Coins` randomness extraction, ML-KEM key generation, and `hdr` / `ek` / `dk` heap
allocations (`+372..+684`) for `spqr::send::<signal_session_ratchet::Coins>`.
-/

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc hiding AllocContracts4K
open CryptoVerification.Cli.LibsignalSpqrV1.M4 (AllocContracts4K)

open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16

open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  (ls_lemma% fnOff "signal_session_coins_fill")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::mac_hdr")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")
  (ls_stub% "libsignal_session_rng_fill")
  (ls_hook% "libsignal_session_rng_fill")
  (ls_stub% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed")
  (ls_hook% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed")
  (ls_stub% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1")
  (ls_hook% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1")
  (ls_stub% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2")
  (ls_hook% "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate1")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::encapsulate1")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "memset")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")

private theorem session_memset_region_of_alloc4K {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts4K b A ext)
    (stk : Nat) (hstk : allocHookStack ≤ stk) (hstk' : stk ≤ 2 ^ 64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SignalSession.Coins.coinsFillName +
        BitVec.ofNat 64 (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill")))
      (withStack sessionMemsetRegionSpec stk) := by
  have h := hA.session_memset_ok_at CryptoVerification.SignalSession.Coins.coinsFillName
    (num% (ls_off% "memset" - ls_off% "signal_session_coins_fill"))
    stk hstk hstk'
    (by rw [(ls_lemma% fnOff "signal_session_coins_fill"), (ls_stub% "memset")])
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (sessionMemsetSpec stk).pre x s0 ∗ R := by
    dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      sessionMemsetSpec, libcMemsetSpec] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩,
      Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hpre.2⟩
  refine h.mono_outcome x R s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemsetRegionSpec, memsetRegionSpec,
      sessionMemsetSpec, libcMemsetSpec] at hpost ⊢
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
  · exact (not_satisfies_false_sepConj hpan.2).elim
  · rcases hex with ⟨_, _, hex'⟩ | ⟨_, hoom⟩
    · exact (not_satisfies_false_sepConj hex').elim
    · exact (not_satisfies_false_sepConj hoom).elim

/-- The `spqr::send` call site of `signal_session_coins_fill` meets `coinsFillSpec b spqrSendCalleeStack`
    under 4K-stack `AllocContracts4K`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_coinsFill_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "signal_session_coins_fill"))
      (CryptoVerification.SignalSession.Coins.coinsFillSpec b spqrSendCalleeStack) := by
  have hfn : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.SignalSession.Coins.coinsFillName)
      (CryptoVerification.SignalSession.Coins.coinsFillSpec b spqrSendCalleeStack) :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegB.BS10.coinsFill_ok_of_mem_hooks
      hb spqrSendCalleeStack (by decide) (by decide)
      (hA.session_memcpy_region_ok_at CryptoVerification.SignalSession.Coins.coinsFillName
        (num% (ls_off% "memcpy" - ls_off% "signal_session_coins_fill"))
        (spqrSendCalleeStack - 80) (by decide) (by decide)
        (by rw [(ls_lemma% fnOff "signal_session_coins_fill"), (ls_stub% "memcpy")]))
      (session_memset_region_of_alloc4K hA (spqrSendCalleeStack - 80) (by decide) (by decide))
  exact sub_ok_at_of_fnAddr hfn CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "signal_session_coins_fill"))
    (by fnoff_eq)

/-- The `spqr::send` call site of `signal_session_coins_fill` meets `coinsFillSpec b spqrSendCalleeStack`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_coinsFill_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (hb : b &&& 0xfff#64 = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "signal_session_coins_fill"))
      (CryptoVerification.SignalSession.Coins.coinsFillSpec b spqrSendCalleeStack) :=
  CryptoVerification.SignalSession.Coins.coinsFill_ok_at hA hb spqrSendCalleeStack (by decide) (by decide)
    CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "signal_session_coins_fill"))
    (by fnoff_eq)

/-- `coinsAt b cur tape` entails `coinsAfter b cur tape 0` (drops `tape.length < 2 ^ 63`). -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.coinsAt_entails_coinsAfter_zero (b cur : BitVec 64) (tape : List (BitVec 8)) :
    CryptoVerification.SignalSession.Coins.coinsAt b cur tape ⊢
      CryptoVerification.SignalSession.Coins.coinsAfter b cur tape 0 := by
  unfold CryptoVerification.SignalSession.Coins.coinsAt CryptoVerification.SignalSession.Coins.tapeAt2 CryptoVerification.SignalSession.Coins.coinsAfter CryptoVerification.SignalSession.Coins.tapeAfter2
  apply Entails.pure_left; intro _
  simp only [BitVec.add_zero, Nat.sub_zero]
  exact Entails.refl _

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemFromSeed_ok {b : BitVec 64} {K : MlKem} {ext : String → Option (State → State)}
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed"))
      (mlkemFromSeedSpec K) :=
  hook_ok_at (hname := mlkemFromSeedName) rfl
    (by fnoff_eq) (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, mlkemFromSeedName]) hseed

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemPk1_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1"))
      mlkemPk1Spec :=
  hook_ok_at (hname := mlkemPk1Name) rfl
    (by fnoff_eq) (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, mlkemPk1Name]) hpk1

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemPk2_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2"))
      mlkemPk2Spec :=
  hook_ok_at (hname := mlkemPk2Name) rfl
    (by fnoff_eq) (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, mlkemPk2Name]) hpk2

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_macHdr_ok {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : AuthMacHdrPinnedOkX img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::authenticator::Authenticator>::mac_hdr" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((authMacHdrPinnedSpec F A).inImage img) :=
  by
    have h1 := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
    have h2 := (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::mac_hdr")
    have heq : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% ((2^64 + ls_off% "<spqr::authenticator::Authenticator>::mac_hdr" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64) =
        (tripleRatchetProgAtExt img.base ext).fnAddr authMacHdrName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, authMacHdrName, h1, h2]; bv_omega
    rw [heq]; exact h

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_doReserve2_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : CryptoVerification.Cli.SpqrV1.Top.Send.DoReserve2OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
      ((doReserve1Raw32Spec A).inImage img) :=
  sub_ok_at_of_fnAddr h CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#7]"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encodeBytes_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : EncodeBytesOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((encodeBytesSpecX A).inImage img) :=
  by
    have h1 := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
    have h2 := (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")
    have heq : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% ((2^64 + ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64) =
        (tripleRatchetProgAtExt img.base ext).fnAddr encodeBytesName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, encodeBytesName, h1, h2]; bv_omega
    rw [heq]; exact h

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_polyNextChunk_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : PolyNextChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% ((2^64 + ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64))
      ((polyNextChunkSpec A img.base).inImage img) :=
  by
    have h1 := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
    have h2 := (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")
    have heq : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% ((2^64 + ls_off% "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>") % 2^64) =
        (tripleRatchetProgAtExt img.base ext).fnAddr polyNextChunkName := by
      simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName, polyNextChunkName, h1, h2]; bv_omega
    rw [heq]; exact h

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_encapsulate1_ok {b : BitVec 64} {K : MlKem} {ext : String → Option (State → State)}
    (henc : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "libcrux_ml_kem::mlkem768::incremental::encapsulate1"))
      (mlkemEncaps1Spec K) :=
  hook_ok_at (hname := mlkemEncaps1Name) rfl
    (by fnoff_eq) (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, mlkemEncaps1Name]) henc

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_shim_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      sessionShimSpec :=
  hA.shim_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_alloc_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_dealloc_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_region_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
    (by rw [(ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>"), libsignalSessionCode_fnOff_memcpy])

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_shim_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      sessionShimSpec :=
  hA.shim_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_alloc_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_dealloc_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_dealloc"))
    (by fnoff_eq)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_region_ok_ext
    {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName +
        bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
      (withStack sessionMemcpyRegionSpec spqrSendCalleeStack) :=
  hA.session_memcpy_region_ok_at CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName
    (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "memcpy"))
    spqrSendCalleeStack (by decide) (by decide)
    (by rw [(ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>"), libsignalSessionCode_fnOff_memcpy])

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_handle_error {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) = some Rust.panicked :=
  panic_at_handle_error_ext b ext CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName (num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error"))
    (by
      change libsignalSessionCode.fnOff CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + num% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error") =
        libsignalSessionCode.fnOff "alloc::raw_vec::handle_error"
      rw [(ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>"), (ls_stub% "alloc::raw_vec::handle_error")])

/-- Sub-step 1a (`entry + 372#64 -> entry + 512#64`) under 4K-stack `AllocContracts4K`:
    copies `epoch` and inline `Authenticator` words, fills 64-byte `seed` via `signal_session_coins_fill`,
    generates 2400-byte ML-KEM keypair via `from_seed` at `sp + 4704#64`, and calls `pk1`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_372_to_512_ext
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext) (hb : img.base &&& 0xfff#64 = 0#64)
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64)
    (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 512#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) sf
        ((authenticatorPinAt A g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) s P post := by
  have hrng_call := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_coinsFill_ok_ext (b := img.base) hA hb
  have hseed_call := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemFromSeed_ok (b := img.base) hseed
  have hpk1_call := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemPk1_ok (b := img.base) hpk1
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 372 140
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  rw [ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 48) (k := 352) (b' := sp + 7184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 7184#64),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide),
      memRegion_64_eq_words8 (sp + 4192#64),
      memRegion_48_eq_words6 (sp + 7136#64),
      memRegion_64_eq_words8 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 23 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine SepWP.fold (words8At_entails_memRegion (sp + 7536#64) _ _ _ _ _ _ _ _)
    (by dsimp only [words8At]; sep_focus) ?_
  refine SepWP.fold (CryptoVerification.Cli.SpqrV1.Top.Send.coinsAt_entails_coinsAfter_zero img.base cur tape) (by sep_focus) ?_
  wp_apply
  wp_conv_pre => rw [List.take_append_of_le_length h64, Nat.min_eq_left h64, ← hseed_val]
  obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7, hseed_words⟩ :=
    exists_words8_of_len64 seed.toList (List.Vector.toList_length seed)
  wp_conv_pre => rw [hseed_words (sp + 7536#64)]; dsimp only [words8At]
  wp_steps
  have hfold_seed_4192 :
      words8At (sp + 4192#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ⊢ ((sp + 4192#64) ↦ₛ seed.toList) := by
    rw [hseed_words (sp + 4192#64)]
    exact Entails.refl _
  refine SepWP.fold hfold_seed_4192 (by dsimp only [words8At]; sep_focus) ?_
  clear hseed_words hfold_seed_4192
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
  wp_apply; wp_steps; wp_apply; wp_steps
  refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
    (by simp only [‹sf_1.sp = _›, ‹sf.sp = _›, hsp]; sep_focus) ?_
  have hfold_end :
      authInlineWordsAt g (sp + 7136#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 7184#64) ↦₆₄ epoch) ∗
      memRegion (sp + 7192#64) 344 ∗
      ((sp + 4192#64) ↦ₛ seed.toList) ∗
      memRegion (sp + 4256#64) 440 ∗
      words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
      memRegion (sp + 7600#64) 336 ⊢
      authenticatorPinAt A g (sp + 7136#64) auth ∗
      memRegion (sp + 7184#64) 352 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 7536#64) 400 := by
    rw [authenticatorPinAt_eq_inline_heap A g (sp + 7136#64) auth,
        ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (sp + 7184#64),
        ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide)]
    have h7184 : ((sp + 7184#64) ↦₆₄ epoch) ⊢ ∃∗ d : BitVec 64, (sp + 7184#64) ↦₆₄ d :=
      Entails.sepExists_right _ (Entails.refl _)
    have h4192 := pointsToBytes_entails_memRegion (sp + 4192#64) seed.toList
    rw [List.Vector.toList_length] at h4192
    simp only [sepConj_assoc]
    exact sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono h7184
          (sepConj_mono (Entails.refl _)
            (sepConj_mono h4192
              (sepConj_mono (Entails.refl _)
                (sepConj_mono (words8At_entails_memRegion (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7)
                  (Entails.refl _)))))))
  refine SepWP.fold hfold_end
    (by dsimp only [authInlineWordsAt, words8At]; sep_focus) ?_
  refine finish_sepWP
    (hnext _
      (by wp_norm_goal)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by ac_rfl))

/-- Sub-step 1b (`entry + 512#64 -> entry + 684#64`) under 4K-stack `AllocContracts4K`:
    allocates 64-byte `hdr` buffer, 1152-byte `ek` buffer, and 2400-byte `dk` buffer,
    copies `pk1`, `pk2`, and `dk` from `sp + 4704#64`, and prepares arguments for `mac_hdr`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_512_to_684_ext
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K img.base A ext)
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64)
    (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      ImgCallInv img sf →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 684#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 →
      sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr →
      sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr →
      sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((A.live hdr_ptr 64 1 ∗
          (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_shim_ok_ext hA
  have halloc := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_alloc_ok_ext hA
  have hmemcpy := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_memcpy_region_ok_ext hA
  have hpk2_call := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_mlkemPk2_ok (b := img.base) hpk2
  have haerr := CryptoVerification.Cli.SpqrV1.Top.Send.spqrSend_handle_error (b := img.base) (ext := ext)
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 512 172
  spqr_send_fetches_range_cli img.base (Rust.withPanics ext) 13576 60
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName = entry
  examples_hide_fetches; subst hP
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc")) img hinv
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAlloc_inImage halloc 64 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := entry + 528#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) img hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc")) img hinv_ok1
    obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hpk1_words⟩ :=
      exists_words8_of_len64 (K.fromSeed seed).1.toList (List.Vector.toList_length _)
    wp_conv_pre =>
      rw [pointsToBytes_2400_expose_pk1 sp seed hpk1_slice,
          hpk1_words (sp + 7008#64),
          memRegion_64_eq_words8 (sf1.readReg64 (Reg.gpr 0#5))]
      dsimp only [words8At]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 8 (apply SepWP.exists_elim; intro _)
    wp_steps
    have hfold_pk1 :
        words8At (sf1.readReg64 (Reg.gpr 0#5)) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
        words8At (sp + 7008#64) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
        (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 2304)) ∗
         ((sp + 7072#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 2304).drop 64))) ⊢
        ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗
        ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
      rw [← hpk1_words (sf1.readReg64 (Reg.gpr 0#5)),
          ← hpk1_words (sp + 7008#64),
          pointsToBytes_2400_expose_pk1 sp seed hpk1_slice]
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.fold hfold_pk1 (by dsimp only [words8At]; sep_focus) ?_
    clear hpk1_words hfold_pk1
    refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
    wp_apply; wp_steps
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
      (by simp only [hsp1]; sep_focus) ?_
    wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_rustAlloc_inImage halloc 1152 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := entry + 584#64) (sp_call := sp) hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) img hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "__rustc::__rust_alloc")) img hinv_ok2
      have hek_mem : memRegion (sf2.readReg64 (Reg.gpr 0#5)) 1152 =
          memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length := by
        rw [hek_len]
      wp_conv_pre => rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, hek_mem]
      wp_steps; wp_apply; wp_steps
      wp_conv_pre => simp only [hsp2]
      have hfold_ek :
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 1152 1 ∗
          ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
          ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
          (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 1152)) ∗
           ((sp + 7008#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 1152).drop 1152))) ⊢
          RustHeap.vecU8Buf A 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
        rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, ← sepConj_assoc]
        exact sepConj_mono
          (live_pointsTo_entails_vecU8Buf (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList
            1152 hek_len (by decide) (by decide) hne0_2)
          (Entails.refl _)
      refine SepWP.fold hfold_ek (by sep_focus) ?_
      wp_apply; wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro hinv3
      refine call_rustAlloc_inImage halloc 2400 ⟨by decide, ⟨0, rfl⟩, by decide⟩
        (s0 := s0) (ret_pc := entry + 620#64) (sp_call := sp) hinv3
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
        (by sep_focus)
        (fun sf3 hinv_oom3 hpc3 hrun3 hsp3 _ h0_3 htr_oom3 => ?_)
        (fun sf3 hinv_ok3 hpc3 hrun3 hsp3 hcs3 hne0_3 h0b_3 htr_ok3 => ?_)
      · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_cli_ratchet::Coins>" "alloc::raw_vec::handle_error")) img hinv_oom3
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        intro _
        exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [arm64_norm, *])
      · rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
        simp only [wp_norm, arm64_norm, *] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3 hvregs_3
        apply of_sepWP_inImage (mid := entry + 684#64) img hinv_ok3
        have hdk_mem : memRegion (sf3.readReg64 (Reg.gpr 0#5)) 2400 =
            memRegion (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList.length := by
          rw [hdk_len]
        wp_conv_pre => rw [hdk_mem]
        wp_steps; wp_apply; wp_steps
        wp_conv_pre => simp only [hsp3]
        have hfold_dk :
            A.live (sf3.readReg64 (Reg.gpr 0#5)) 2400 1 ∗
            ((sf3.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
            ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ⊢
            RustHeap.vecU8Buf A 2400#64 (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList ∗
            memRegion (sp + 4704#64) 2400 := by
          have h4704 := pointsToBytes_entails_memRegion (sp + 4704#64) (K.fromSeed seed).2.2.toList
          rw [hdk_len] at h4704
          rw [← sepConj_assoc]
          exact sepConj_mono
            (live_pointsTo_entails_vecU8Buf (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList
              2400 hdk_len (by decide) (by decide) hne0_3)
            h4704
        refine SepWP.fold hfold_dk (by sep_focus) ?_
        refine finish_sepWP_inImage (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (fun hinv4 => hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) (sf3.readReg64 (Reg.gpr 0#5))
            hinv4 hne0_1 h0b_1
            (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            (by simp only [State.sp, arm64_norm, *])
            (by simp only [Reg.x0, arm64_norm, *])
            (by simp only [Reg.x1, arm64_norm, *])
            (by simp only [Reg.x2, arm64_norm, *])
            (by simp only [Reg.x3, arm64_norm, *])
            (by simp only [Reg.x8, arm64_norm, *])
            (by simp only [Reg.x19, arm64_norm, *])
            (by simp only [Reg.x20, arm64_norm, *])
            (by simp only [Reg.x21, arm64_norm, *])
            (by simp only [Reg.x22, arm64_norm, *])
            (by simp only [Reg.x23, arm64_norm, *])
            (by simp only [Reg.x24, arm64_norm, *])
            (by simp only [Reg.x25, arm64_norm, *])
            (by simp only [Reg.x26, arm64_norm, *])
            (by simp only [Reg.x27, arm64_norm, *])
            (by simp only [Reg.x28, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (Entails.of_eq (by ac_rfl))

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_372_to_512
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) (hb : img.base &&& 0xfff#64 = 0#64)
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K))
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec)
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (sp cur : BitVec 64) (tape : List (BitVec 8)) (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64) (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64) (htrace : s.trace = s0.trace)
    (hP : P = (authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 512#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) sf
        ((authenticatorPinAt A g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ memRegion (sp + 7536#64) 400 ∗
          CryptoVerification.SignalSession.Coins.coinsAfter img.base cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 3068#64) s P post :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_372_to_512_ext
    (AllocContracts4K.of_AllocContracts hA) hb hseed hpk1 g auth epoch sp cur tape h64
    seed hseed_val d4056 hsp_align hpc hrun hsp hx24 htrace hP hnext

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_512_to_684
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (sp epoch : BitVec 64) (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 512#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64) (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      ImgCallInv img sf → hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendName + 684#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 → sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr → sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr → sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 → sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          RustHeap.vecU8Buf A 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          RustHeap.vecU8Buf A 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗ A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.step_keysUnsampled_512_to_684_ext
    (AllocContracts4K.of_AllocContracts hA) hpk2 sp epoch seed hpk1_slice hpk2_slice
    hinv hsp_align hpc hrun hsp hx21 hx22 htrace hP hnext

end CryptoVerification.SpqrV1.Top.Send
