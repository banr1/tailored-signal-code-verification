/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `.keysUnsampled` Sub-Steps (`+372..+684`)

**Checked by Lean.**

Verifies `+372..+684` of the inlined `.keysUnsampled` arm of `<States>::send`:
64-byte RNG draw, ML-KEM keypair generation (`from_seed`, `pk1`, `pk2`), and heap allocation
of `hdr` (`64`B), `ek` (`1152`B), and `dk` (`2400`B).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
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
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
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
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")

theorem spqrSend_rngFill_ok {b ctl : BitVec 64} {ext : String → Option (State → State)}
    (hrng : HookSat ext rngFillName (rngFillSpec ctl)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "libsignal_session_rng_fill"))
      (rngFillSpec ctl) :=
  hook_ok_at (hname := rngFillName) rfl
    (by simp only [arm64_norm, spqrSendName, rngFillName]; rfl)
    (by simp only [arm64_norm, rngFillName])
    (fun _ => by simp only [arm64_norm, rngFillName]) (by decide +kernel) hrng

theorem spqrSend_mlkemFromSeed_ok {b : BitVec 64} {K : MlKem} {ext : String → Option (State → State)}
    (hseed : HookSat ext mlkemFromSeedName (mlkemFromSeedSpec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::from_seed"))
      (mlkemFromSeedSpec K) :=
  hook_ok_at (hname := mlkemFromSeedName) rfl
    (by simp only [arm64_norm, spqrSendName, mlkemFromSeedName]; rfl)
    (by simp only [arm64_norm, mlkemFromSeedName])
    (fun _ => by simp only [arm64_norm, mlkemFromSeedName]) (by decide +kernel) hseed

theorem spqrSend_mlkemPk1_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (hpk1 : HookSat ext mlkemPk1Name mlkemPk1Spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk1"))
      mlkemPk1Spec :=
  hook_ok_at (hname := mlkemPk1Name) rfl
    (by simp only [arm64_norm, spqrSendName, mlkemPk1Name]; rfl)
    (by simp only [arm64_norm, mlkemPk1Name])
    (fun _ => by simp only [arm64_norm, mlkemPk1Name]) (by decide +kernel) hpk1

theorem spqrSend_mlkemPk2_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<libcrux_ml_kem::mlkem768::incremental::KeyPairCompressedBytes>::pk2"))
      mlkemPk2Spec :=
  hook_ok_at (hname := mlkemPk2Name) rfl
    (by simp only [arm64_norm, spqrSendName, mlkemPk2Name]; rfl)
    (by simp only [arm64_norm, mlkemPk2Name])
    (fun _ => by simp only [arm64_norm, mlkemPk2Name]) (by decide +kernel) hpk2

theorem spqrSend_macHdr_ok {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : AuthMacHdrPinnedOkX img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::mac_hdr"))
      ((authMacHdrPinnedSpec F A).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::mac_hdr"))
    (by simp only [arm64_norm, spqrSendName, authMacHdrName])

theorem spqrSend_doReserve2_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DoReserve2OkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
      ((doReserve1Raw32Spec A).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]"))
    (by simp only [arm64_norm, spqrSendName, doReserve2Name, (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#2]")])

theorem spqrSend_encodeBytes_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : EncodeBytesOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"))
      ((encodeBytesSpecX A).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes"))
    (by simp only [arm64_norm, spqrSendName, encodeBytesName])

theorem spqrSend_polyNextChunk_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : PolyNextChunkOkX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
      ((polyNextChunkSpec A img.base).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk"))
    (by simp only [arm64_norm, spqrSendName, polyNextChunkName])

theorem spqrSend_encapsulate1_ok {b : BitVec 64} {K : MlKem} {ext : String → Option (State → State)}
    (henc : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "libcrux_ml_kem::mlkem768::incremental::encapsulate1"))
      (mlkemEncaps1Spec K) :=
  hook_ok_at (hname := mlkemEncaps1Name) rfl
    (by simp only [arm64_norm, spqrSendName, mlkemEncaps1Name]; rfl)
    (by simp only [arm64_norm, mlkemEncaps1Name])
    (fun _ => by simp only [arm64_norm, mlkemEncaps1Name]) (by decide +kernel) henc

theorem spqrSend_shim_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      sessionShimSpec :=
  hA.shim_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    (by simp only [arm64_norm, spqrSendName])

theorem spqrSend_alloc_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc"))
      (rustAllocSpec A) :=
  hA.alloc_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc"))
    (by simp only [arm64_norm, spqrSendName])

theorem spqrSend_dealloc_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
    (by simp only [arm64_norm, spqrSendName])

theorem spqrSend_memcpy_region_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy"))
      sessionMemcpyRegionSpec :=
  hA.session_memcpy_region_ok_at spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "memcpy"))
    (by rw [(ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>"), libsignalSessionCode_fnOff_memcpy])

theorem spqrSend_handle_error {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) = some Rust.panicked :=
  panic_at_handle_error_ext b ext spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error"))
    (by
      change libsignalSessionCode.fnOff spqrSendName + num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error") =
        libsignalSessionCode.fnOff "alloc::raw_vec::handle_error"
      rw [(ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>"), (ls_stub% "alloc::raw_vec::handle_error")])

theorem stackAt_spqrSendCallee_to_extHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack ⊢
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp extHookStack := by
  rw [stackAt_spqrSendCallee_split sp extHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_from_extHook (sp : BitVec 64) :
    memRegion (sp - 123008#64) 106624 ∗ stackAt sp extHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [stackAt_spqrSendCallee_split sp extHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_to_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack ⊢
    memRegion (sp - 123008#64) 118912 ∗ stackAt sp allocHookStack := by
  rw [stackAt_spqrSendCallee_split sp allocHookStack (by decide)]
  exact Entails.refl _

theorem stackAt_spqrSendCallee_from_allocHook (sp : BitVec 64) :
    memRegion (sp - 123008#64) 118912 ∗ stackAt sp allocHookStack ⊢
    stackAt sp spqrSendCalleeStack := by
  rw [stackAt_spqrSendCallee_split sp allocHookStack (by decide)]
  exact Entails.refl _

theorem finish_oom_panic {prog : Program} {target_pc : BitVec 64}
    {s0 s : State} {P R : SepProp}
    {post : State → SepProp → Prop}
    (hextern : prog.externAt? s.pc = some Rust.panicked)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  refine SepWPp.panic hrun hextern fun hm => ?_
  simpa only [sepConj_assoc] using
    allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, htr])) hm

theorem call_rustAlloc_inImage {A : RustAlloc} {prog : Program} {img : Obj.Image}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustAllocSpec A))
    (size : Nat) (hlay : LayoutOk size 1)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry_alloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = 1)
    (hsplit : P = (A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hoom : ∀ sf : State, ImgCallInv img sf →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) = 0 →
      sf.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp prog target_pc sf
        ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))
    (hok : ∀ sf : State, ImgCallInv img sf →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 →
      (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rw [hsplit]
  refine of_sepWP_inImage (mid := ret_pc) img hinv ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine call_rustAlloc hcall size 1 hlay (s0 := s0) (ret_pc := ret_pc) (sp_call := sp_call)
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
  apply SepWP.done hpc1 hrun1
  intro hinv1
  by_cases h0 : sf1.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
    have hassoc :
        stackAt sp_call spqrSendCalleeStack ∗
          ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ A.pool ∗ Frame =
        ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    refine ProofLib.SepWPp.pure_elim fun htr_oom => ?_
    exact hoom sf1 hinv1 hpc1 hrun1 hsp1 hcs1 h0 htr_oom
  · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
    have hassoc :
        stackAt sp_call spqrSendCalleeStack ∗
          ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool ∗ Frame =
        ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
          ((A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
    rw [hassoc]
    refine ProofLib.SepWPp.pure_elim fun htr_ok => ?_
    have h0b : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne h0
    exact hok sf1 hinv1 hpc1 hrun1 hsp1 hcs1 h0 h0b htr_ok.2

/-- Eight consecutive 64-bit words (`64` bytes) at `a`. -/
def words8At (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
  ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7)

theorem words8At_entails_memRegion (a : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    words8At a w0 w1 w2 w3 w4 w5 w6 w7 ⊢ memRegion a 64 := by
  unfold words8At
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 56) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 48) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 40) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 32) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 24) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 16) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 8) (b' := a + 56#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
              (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
                (ProofLib.pointsTo64_entails_memRegion _ _)))))))

theorem memRegion_64_eq_words8 (a : BitVec 64) :
    memRegion a 64 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) ∗
      (∃∗ d6 : BitVec 64, (a + 48#64) ↦₆₄ d6) ∗
      (∃∗ d7 : BitVec 64, (a + 56#64) ↦₆₄ d7) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 56) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 48) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 40) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 32) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 24) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 16) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 8) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64),
      ProofLib.memRegion_eight (a + 48#64), ProofLib.memRegion_eight (a + 56#64)]

theorem exists_words8_of_len64 (bs : List (BitVec 8)) (h : bs.length = 64) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) = words8At a w0 w1 w2 w3 w4 w5 w6 w7 := by
  have h1 : (bs.take 32).length = 32 := by rw [List.length_take]; omega
  have h2 : (bs.drop 32).length = 32 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, hw1⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 (bs.take 32) h1
  obtain ⟨w4, w5, w6, w7, hw2⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 (bs.drop 32) h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, fun a => ?_⟩
  rw [← List.take_append_drop 32 bs, pointsToBytes_append a (bs.take 32) (bs.drop 32), h1,
      hw1, hw2,
      CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq a,
      CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq (a + 32#64)]
  unfold words8At
  rw [show (a + 32#64) + 8#64 = a + 40#64 by bv_omega,
      show (a + 32#64) + 16#64 = a + 48#64 by bv_omega,
      show (a + 32#64) + 24#64 = a + 56#64 by bv_omega]
  ac_rfl

theorem pointsToBytes_2400_expose_pk1 {K : MlKem} (sp : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1 : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList) :
    let dk := (K.fromSeed seed).2.2.toList
    ((sp + 4704#64) ↦ₛ dk) =
      ((sp + 7008#64) ↦ₛ (K.fromSeed seed).1.toList) ∗
      (((sp + 4704#64) ↦ₛ dk.take 2304) ∗
       ((sp + 7072#64) ↦ₛ (dk.drop 2304).drop 64)) := by
  intro dk
  have hlen : dk.length = 2400 := List.Vector.toList_length _
  have h1 : (dk.take 2304).length = 2304 := by rw [List.length_take]; omega
  have h2 : ((dk.drop 2304).take 64).length = 64 := by rw [List.length_take, List.length_drop]; omega
  conv_lhs => rw [← List.take_append_drop 2304 dk, ← List.take_append_drop 64 (dk.drop 2304)]
  rw [pointsToBytes_append (sp + 4704#64) (dk.take 2304), h1,
      show (sp + 4704#64) + 2304#64 = sp + 7008#64 by bv_omega,
      pointsToBytes_append (sp + 7008#64) ((dk.drop 2304).take 64), h2,
      show (sp + 7008#64) + 64#64 = sp + 7072#64 by bv_omega,
      hpk1]
  ac_rfl

theorem pointsToBytes_2400_expose_pk2 {K : MlKem} (sp : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk2 : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList) :
    let dk := (K.fromSeed seed).2.2.toList
    ((sp + 4704#64) ↦ₛ dk) =
      ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
      (((sp + 4704#64) ↦ₛ dk.take 1152) ∗
       ((sp + 7008#64) ↦ₛ (dk.drop 1152).drop 1152)) := by
  intro dk
  have hlen : dk.length = 2400 := List.Vector.toList_length _
  have h1 : (dk.take 1152).length = 1152 := by rw [List.length_take]; omega
  have h2 : ((dk.drop 1152).take 1152).length = 1152 := by rw [List.length_take, List.length_drop]; omega
  conv_lhs => rw [← List.take_append_drop 1152 dk, ← List.take_append_drop 1152 (dk.drop 1152)]
  rw [pointsToBytes_append (sp + 4704#64) (dk.take 1152), h1,
      show (sp + 4704#64) + 1152#64 = sp + 5856#64 by bv_omega,
      pointsToBytes_append (sp + 5856#64) ((dk.drop 1152).take 1152), h2,
      show (sp + 5856#64) + 1152#64 = sp + 7008#64 by bv_omega,
      hpk2]
  ac_rfl

/-- Unused stack padding slots within `[sp + 3328, sp + 7936)` during `.keysUnsampled`. -/
@[irreducible] def keysUnsampledUnusedAt (sp : BitVec 64) : SepProp :=
  memRegion (sp + 3328#64) 224 ∗
  memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4184#64) 8 ∗
  memRegion (sp + 4696#64) 8 ∗
  memRegion (sp + 7128#64) 8

theorem memRegion_4608_split_keysUnsampled (sp : BitVec 64) :
    memRegion (sp + 3328#64) 4608 =
      keysUnsampledUnusedAt sp ∗
      memRegion (sp + 3552#64) 504 ∗
      (∃∗ d4056 : BitVec 64, (sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4192#64) 504 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      memRegion (sp + 7136#64) 400 ∗
      memRegion (sp + 7536#64) 400 := by
  unfold keysUnsampledUnusedAt
  rw [ProofLib.memRegion_split' (b := sp + 3328#64) (n := 224) (k := 4384) (b' := sp + 3552#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 3552#64) (n := 504) (k := 3880) (b' := sp + 4056#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4056#64) (n := 8) (k := 3872) (b' := sp + 4064#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4064#64) (n := 16) (k := 3856) (b' := sp + 4080#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4080#64) (n := 104) (k := 3752) (b' := sp + 4184#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4184#64) (n := 8) (k := 3744) (b' := sp + 4192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 504) (k := 3240) (b' := sp + 4696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4696#64) (n := 8) (k := 3232) (b' := sp + 4704#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 4704#64) (n := 2400) (k := 832) (b' := sp + 7104#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7104#64) (n := 24) (k := 808) (b' := sp + 7128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7128#64) (n := 8) (k := 800) (b' := sp + 7136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 400) (k := 400) (b' := sp + 7536#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 4056#64)]
  ac_rfl

theorem rngFill_take64_eq (ctl cur dst : BitVec 64) (rest : List (BitVec 8))
    (h64 : 64 ≤ rest.length) :
    (dst ↦ₛ (rest ++ List.replicate 64 0#8).take 64) ∗ tapeAfter ctl cur rest (min 64 rest.length) =
      (dst ↦ₛ rest.take 64) ∗ tapeAfter ctl cur rest 64 := by
  rw [List.take_append_of_le_length h64, Nat.min_eq_left h64]

theorem live_pointsTo_entails_vecU8Buf {A : RustAlloc} (ptr : BitVec 64) (bs : List (BitVec 8))
    (size : Nat) (hlen : bs.length = size) (hpos : 0 < size) (hlt : size < 2 ^ 63)
    (hptr : ptr ≠ 0) :
    A.live ptr size 1 ∗ (ptr ↦ₛ bs) ⊢
    RustHeap.vecU8Buf A (BitVec.ofNat 64 size) ptr bs := by
  have htoNat : (BitVec.ofNat 64 size).toNat = size := Nat.mod_eq_of_lt (by omega)
  have hne0 : BitVec.ofNat 64 size ≠ 0 := by
    intro h0
    have := congrArg BitVec.toNat h0
    rw [htoNat] at this
    change size = 0 at this
    omega
  unfold RustHeap.vecU8Buf
  simp only [hne0, ↓reduceIte, htoNat, hlen, Nat.sub_self,
    ProofLib.memRegion_zero, sepConj_emp, emp_sepConj]
  exact Entails.pure_right ⟨Nat.le_refl size, hlt, hptr⟩ (Entails.of_eq (by ac_rfl))

theorem fold_vecU8_at (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  have heq :
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs =
      vecU8At A a cap ptr bs := by
    unfold vecU8At vecHeader RustHeap.vecU8Buf
    have hp : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
        (ptr ≠ 0 ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63) := propext ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨h1, h2, h3⟩⟩
    rw [hp]
    by_cases hc : cap = 0 <;> simp only [hc, ↓reduceIte] <;> ac_rfl
  rw [heq]
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem memRegion_48_eq_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ d4 : BitVec 64, (a + 32#64) ↦₆₄ d4) ∗
      (∃∗ d5 : BitVec 64, (a + 40#64) ↦₆₄ d5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]

/-- Sub-step 1a (`entry + 372#64 -> entry + 512#64`):
    copies `epoch` and inline `Authenticator` words, fills 64-byte `seed` via `rng_fill`,
    generates 2400-byte ML-KEM keypair via `from_seed` at `sp + 4704#64`, and calls `pk1`. -/
theorem step_keysUnsampled_372_to_512
    {img : Obj.Image} {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
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
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 372#64)
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
      tapeAt ctl cur tape ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64 →
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
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64) sf
        ((authenticatorPinAt A g (sp + 7136#64) auth ∗
          memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          memRegion (sp + 7536#64) 400 ∗
          tapeAfter ctl cur tape 64 ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3068#64) s P post := by
  have hrng_call := spqrSend_rngFill_ok (b := img.base) hrng
  have hseed_call := spqrSend_mlkemFromSeed_ok (b := img.base) hseed
  have hpk1_call := spqrSend_mlkemPk1_ok (b := img.base) hpk1
  spqr_send_fetches_range img.base (Rust.withPanics ext) 372 140
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
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

/-- Sub-step 1b (`entry + 512#64 -> entry + 684#64`):
    allocates 64-byte `hdr` buffer, 1152-byte `ek` buffer, and 2400-byte `dk` buffer,
    copies `pk1`, `pk2`, and `dk` from `sp + 4704#64`, and prepares arguments for `mac_hdr`. -/
theorem step_keysUnsampled_512_to_684
    {img : Obj.Image} {K : MlKem} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hpk2 : HookSat ext mlkemPk2Name mlkemPk2Spec)
    (sp epoch : BitVec 64)
    (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 512#64)
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
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 684#64 →
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
  have hshim := spqrSend_shim_ok hA
  have halloc := spqrSend_alloc_ok hA
  have hmemcpy := spqrSend_memcpy_region_ok hA
  have hpk2_call := spqrSend_mlkemPk2_ok (b := img.base) hpk2
  have haerr := spqrSend_handle_error (b := img.base) (ext := ext)
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  spqr_send_fetches_range img.base (Rust.withPanics ext) 512 172
  spqr_send_fetches_range img.base (Rust.withPanics ext) 13576 60
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv
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
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv_ok1
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
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv_ok2
      have hek_mem : memRegion (sf2.readReg64 (Reg.gpr 0#5)) 1152 =
          memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length := by
        rw [hek_len]
      wp_conv_pre => rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, hek_mem]
      wp_steps; wp_apply; wp_steps
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
      · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom3
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

end CryptoVerification.SpqrV1.Top.Send











