/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGet
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `KeyHistory::get` Proofs for `<spqr::chain::Chain>::recv_key`

Proves the `KeyHistory::get` entry (`+276`, `0x609e4`), linear-scan loop (`+740`, `0x60bb4`),
and swap-remove hit continuation (`+788`, `0x60be4`) for `<spqr::chain::Chain>::recv_key`
(Block `366`) in fixed-image and relocatable `[LibsignalPlacement]` forms.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout
open ChainAddEpochFacts ChainNewFacts NextKeyInternalFacts ChainSendKeyFacts
open RecvKeyDecodes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  nextKeyInternal_fnOff chainRecvKey_fnOff doReserve7_fnOff
  shim_fnOff alloc_fnOff dealloc_fnOff handleError_fnOff
  panicAddOverflow_fnOff panicSubOverflow_fnOff
  corePanic_fnOff assertFailedUsize_fnOff expectFailed_fnOff sliceIndexFail_fnOff
  libsignalSessionCode_fnOff_0x5a99c
  libsignalSessionCode_fnOff_0x4dca8
  libsignalSessionCode_fnOff_0x5b4d8
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_add_overflow")
  (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")
  (ls_hook% "core::panicking::panic_const::panic_const_sub_overflow")
  (ls_stub% "core::panicking::assert_failed::<usize, usize>")
  (ls_hook% "core::panicking::assert_failed::<usize, usize>")
  (ls_stub% "core::panicking::panic")
  (ls_hook% "core::panicking::panic")
  (ls_stub% "core::option::expect_failed")
  (ls_hook% "core::option::expect_failed")
  (ls_stub% "core::slice::index::slice_index_fail")
  (ls_hook% "core::slice::index::slice_index_fail")

theorem panic_at_assert_recvKey (base : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr chainRecvKeyName +
        bv% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5b4d8)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext chainRecvKeyName assertFailedUsizeName
    (num% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5b4d8))
    (by rw [chainRecvKey_fnOff, assertFailedUsize_fnOff])
    (hp := by simp [Rust.isPanicSymbol, assertFailedUsizeName])

theorem panic_at_add_ovf_recvKey (base : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr chainRecvKeyName +
        bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5b4d8)) =
      some Rust.panicked := by
  exact panic_at_sym_ext base ext chainRecvKeyName panicAddOverflowName
    (num% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5b4d8))
    (by rw [chainRecvKey_fnOff, panicAddOverflow_fnOff])
    (hp := by simp [Rust.isPanicSymbol, panicAddOverflowName])

theorem panic_at_handle_error_recvKey (base : BitVec 64) (ext : String → Option (State → State)) :
    (libsignalSessionCode.rebase base (Rust.withPanics ext)).externAt?
      ((libsignalSessionCode.rebase base (Rust.withPanics ext)).fnAddr chainRecvKeyName +
        bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5b4d8)) =
      some Rust.panicked :=
  panic_at_handle_error_ext base ext chainRecvKeyName
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x5b4d8))
    (by rw [chainRecvKey_fnOff, handleError_fnOff])

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

/-! ## Outer `Chain` Frame Bundle while `link.recv` is Open -/

/-- Untouched `Chain` fields while `x.self.links[epochIndex].recv` is unpacked. -/
def chainOuterRecvAt (A : RustAlloc) (x : ChainRecvKeyGhost)
    (epochIndex : Nat) (hi : epochIndex < x.self.links.length) (gce : ChainEpochGhost) : SepProp :=
  let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
  let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
  (x.selfPtr ↦₆₄ x.G.linksCap) ∗ ((x.selfPtr + 8#64) ↦₆₄ x.G.linksPtr) ∗
    ((x.selfPtr + 16#64) ↦₆₄ x.G.linksHead) ∗
    ((x.selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 x.self.links.length) ∗
    A.live x.G.linksPtr (x.G.linksCap.toNat * 112) 8 ∗
    chainEpochDirectionAt A epPtr gce.send (x.self.links[epochIndex]'hi).send ∗
    vecDequeSlotsExcept (chainEpochAt A) 112 x.G.linksCap.toNat x.G.linksHead.toNat
      x.G.linksPtr (x.G.epochs.zip x.self.links) s_idx ∗
    ((x.selfPtr + 56#64) ↦₆₄ x.self.currentEpoch) ∗
    ((x.selfPtr + 64#64) ↦₆₄ x.self.sendEpoch) ∗
    chainRestSendKeyAt A x.selfPtr x.G x.self

/-- Pack `chainOuterRecvAt` + `recv'` vectors/counter into `chainRepr` with `links.set epochIndex`. -/
theorem chainOuterRecvAt_pack (A : RustAlloc) (x : ChainRecvKeyGhost)
    (epochIndex : Nat) (hi : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost) (prevGhost' : VecPin) (recv' : ChainEpochDirection)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    chainOuterRecvAt A x epochIndex hi gce ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv'.next ∗
      vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr recv'.prev.data ∗
      ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
      memRegion (epPtr + 0x6c#64) 4 ⊢
      chainRepr A x.selfPtr
        { x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi with recv := recv' } } := by
  intro s_idx epPtr
  unfold chainOuterRecvAt
  dsimp only
  have hpack := chainRepr_pack_recv A x.selfPtr x.G x.self epochIndex hi gce prevGhost' recv'
    hhead hcap_lt hptr hlen_le hlen_eq
  dsimp only [epPtr, s_idx] at hpack ⊢
  refine Entails.trans ?_ hpack
  exact Entails.of_eq (by ac_rfl)


theorem vecU8At_pack_prev (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs.length ⊢
      vecU8At A a cap ptr bs := by
  unfold vecU8At vecHeader vecU8Rest
  by_cases h0 : cap = 0
  · have hlen0 : bs.length = 0 := by
      have : cap.toNat = 0 := congrArg BitVec.toNat h0
      omega
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero hlen0
    subst hbs
    simp only [h0, ↓reduceIte, pointsToBytes_nil, emp_sepConj, sepConj_emp]
    rw [show ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) ∗
          ⌜[].length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜[].length ≤ (0 : BitVec 64).toNat ∧ (0 : BitVec 64).toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 [].length)) by ac_rfl]
    exact Entails.pure_right ⟨by simp, by decide, hptr⟩ (Entails.refl _)
  · simp only [h0, ↓reduceIte]
    rw [show ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
           (ptr ↦ₛ bs) ∗ (A.live ptr cap.toNat 1 ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) by ac_rfl]
    exact Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _)

theorem chainOuterRecvAt_pack_unchanged (A : RustAlloc) (x : ChainRecvKeyGhost)
    (epochIndex : Nat) (hi : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi).recv
    chainOuterRecvAt A x epochIndex hi gce ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
      ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
      ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
      (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
      vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
      ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
      memRegion (epPtr + 0x6c#64) 4 ⊢
      chainRepr A x.selfPtr x.self := by
  intro s_idx epPtr recv
  have hv := vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
    recv.prev.data hp_le hp_cap hp_ptr
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hv
  have hpack := chainOuterRecvAt_pack A x epochIndex hi gce gce.recv.prev recv
    hhead hcap_lt hptr hlen_le hlen_eq
  dsimp only at hpack
  have hself :
      { x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi with recv := recv } } =
        x.self := by
    have hlink : { x.self.links[epochIndex]'hi with recv := recv } = x.self.links[epochIndex]'hi := rfl
    rw [hlink, List.set_getElem_self]
  rw [hself] at hpack
  refine Entails.trans ?_ hpack
  rw [show chainOuterRecvAt A x epochIndex hi gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 =
      chainOuterRecvAt A x epochIndex hi gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        (((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
         ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
         ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
         (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
         vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length) ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hv))

/-! ## Arithmetic Helpers for `KeyHistory::get` -/

theorem get_loop_idx_props {i len : Nat} (hi36 : i + 36 ≤ len) (hlen_lt : len < 2 ^ 63) :
    (BitVec.ofNat 64 i - 36#64) + 36#64 = BitVec.ofNat 64 i ∧
    (BitVec.ofNat 64 i - 36#64) + 40#64 = BitVec.ofNat 64 (i + 4) ∧
    (BitVec.ofNat 64 len == BitVec.ofNat 64 i) = false ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 4)) = false ∧
    BitVec.ofNat 64 i + 36#64 = BitVec.ofNat 64 (i + 36) ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 36)) = false ∧
    BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 i) = false := by
  refine ⟨by bv_omega, by bv_omega, ?_, ?_, by bv_omega, ?_, ?_⟩
  · rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)] at this
    omega
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i + 4 < 2 ^ 64)]
    exact decide_eq_false (by omega)
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i + 36 < 2 ^ 64)]
    exact decide_eq_false (by omega)
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
    exact decide_eq_false (by omega)

theorem get_swap_idx_props {i len : Nat} (hi36 : i + 36 ≤ len) (hlen_lt : len < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 (i + 36)) = decide ( ¬ (i + 36 < len) ) ∧
    (i + 36 < len →
      BitVec.ofNat 64 len - 36#64 = BitVec.ofNat 64 (len - 36) ∧
      BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len - 36)) = false) := by
  refine ⟨?_, fun hlt => ⟨by bv_omega, ?_⟩⟩
  · simp only [BitVec.ule, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i + 36 < 2 ^ 64)]
    by_cases h : i + 36 < len
    · rw [decide_eq_false (not_not.mpr h)]; exact decide_eq_false (by omega)
    · rw [decide_eq_true h]; exact decide_eq_true (by omega)
  · simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : len - 36 < 2 ^ 64)]
    exact decide_eq_false (by omega)

/-! ## Hit Continuation of `KeyHistory::get` at `+788` (`0x60be4`) -/

set_option maxHeartbeats 800000 in
theorem recvKey_get_hit_from_788 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hi_mod : i % 36 = 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index =
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let recv' := { recv with prev := recv.prev.remove i x.self.params }
      let outKey := (recv.prev.data.drop (i + 4)).take 32
      .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 788#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr)
    (hx25 : s.readReg64 (.gpr 25#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_shim := sub_ok_at_rebase (name := chainRecvKeyName) (callee := shimName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5b4d8))
    (by rw [chainRecvKey_fnOff, shim_fnOff]) hshim
  have h_alloc := sub_ok_at_rebase (name := chainRecvKeyName) (callee := allocName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x5b4d8))
    (by rw [chainRecvKey_fnOff, alloc_fnOff]) halloc
  have h_panic_oom := panic_at_handle_error_recvKey img.base ext
  have h_ok708 := @recvKey_ok_from_708 img hkdf A ext x s0 c3 R
  clear hshim halloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr, recv]
  clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨_, _, _, _, hi_add36, hult_i36, hult_i⟩ := get_loop_idx_props hi36 hbs_lt
  have ⟨hule_swap, hswap_lt⟩ := get_swap_idx_props hi36 hbs_lt
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx19
  wp_norm_hyp hx21
  wp_norm_hyp hx22
  wp_norm_hyp hx23
  wp_norm_hyp hx24
  wp_norm_hyp hx25
  wp_norm_hyp htrace
  wp_norm_hyp hi_add36
  wp_norm_hyp hult_i36
  wp_norm_hyp hult_i
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 816#64) hF ?_
  apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x5b4d8)) hF
  wp_steps
  have hstack_s0 : stackAt (s0.sp - 128#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by
    rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv2
  have ⟨hF2, hsym2⟩ := hinv2
  apply SepWP.seq_inImage (mid := entry_addr + bv% (ls_off% "__rustc::__rust_alloc" - 0x5b4d8)) hinv2
  wp_call h_shim ()
  wp_steps
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  rintro ⟨hF3, hsym3⟩
  wp_call h_alloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    wp_norm_hyp hoom_64
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro htrace_oom
    wp_norm_hyp htrace_oom
    wp_norm_hyp hpost
    apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x5b4d8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_oom) fun hm => ?_
    exact allowPanic_recvKey_oom
      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htrace])) hm
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmod1, htrace1⟩
    wp_norm_hyp htrace1
    let p_key := sf_1.readReg64 (Reg.gpr 0#5)
    have hstack_back :
        memRegion (s.sp - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗ stackAt sf.sp extHookStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_top_split s.sp, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro u0
    apply SepWPp.exists_elim; intro u1
    apply SepWPp.exists_elim; intro u2
    apply SepWPp.exists_elim; intro u3
    obtain ⟨k0, k1, k2, k3, hget_cells⟩ :=
      exists_entry36_get_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i hi36
    have ⟨hbs_get, hkey_pack⟩ := hget_cells gce.recv.prev.ptr
    refine SepWPp.fold (Entails.of_eq hbs_get) (by sep_focus) ?_
    have hsp_sf1 : sf_1.sp = s0.sp - 128#64 := by rw [hsp_sf_1, hsp_sf, hsp]
    have hsp1_align : sf_1.spAligned = true := by
      simp only [State.spAligned, hsp_sf1] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    wp_norm_hyp hsp_sf1
    wp_norm_hyp hsp1_align
    wp_norm_hyp hule_swap
    let outKey := ((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop (i + 4)).take 32
    have houtKey_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.extract (i + 4) (i + 36) = outKey := by
      rw [List.extract_eq_take_drop, show i + 36 - (i + 4) = 32 by omega]
    have houtKey_len : outKey.length = 32 := by
      rw [← houtKey_eq]
      simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
    by_cases hlt_end : i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length
    · have hule_f : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = false :=
        decide_eq_false (not_not.mpr hlt_end)
      have ⟨hsub36, hult_sub36⟩ := hswap_lt hlt_end
      wp_norm_hyp hule_f
      wp_norm_hyp hsub36
      wp_norm_hyp hult_sub36
      obtain ⟨ei0, ei1, ei2, ei3, ei4, el0, el1, el2, el3, el4, hswap_cells⟩ :=
        exists_entry36_swap_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega) (by omega)
      have ⟨hbs_swap_in, hbs_swap_out⟩ := hswap_cells gce.recv.prev.ptr
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 708#64) hinv4 ?_
      apply SepWP.seq_inImage (mid := entry_addr + 840#64) hinv4
      wp_steps
      refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_swap_in) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv5
      wp_steps
      refine SepWP.fold (Entails.of_eq hbs_swap_out) (by sep_focus) ?_
      have hrem := vecU8At_pack_remove_swap A
        (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
        gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params hlt_end hp_le hp_cap hp_ptr
      dsimp only [KeyHistory.KEY_SIZE] at hrem
      have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
      have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
      rw [ha58, ha60] at hrem
      refine SepWP.fold hrem (by sep_focus) ?_
      have hpack := chainOuterRecvAt_pack A x epochIndex hi_ep gce gce.recv.prev
        { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
        hhead hcap_lt hptr hlen_le hlen_eq
      dsimp only at hpack
      refine SepWP.fold hpack (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by rw [← hx26]; wp_norm_goal,
         by rw [← hx27]; wp_norm_goal,
         by rw [← hx28]; wp_norm_goal,
         by wp_norm_goal,
         by wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_
        (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
      rw [houtKey_eq]
      sep_frame
    · have hule_t : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = true :=
        decide_eq_true hlt_end
      wp_norm_hyp hule_t
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 708#64) hinv4 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
      have hrem := vecU8At_pack_remove_last A
        (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
        gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params (by omega) hlt_end hp_le hp_cap hp_ptr
      have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
      have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
      rw [ha58, ha60] at hrem
      refine SepWP.fold hrem (by sep_focus) ?_
      have hpack := chainOuterRecvAt_pack A x epochIndex hi_ep gce gce.recv.prev
        { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
        hhead hcap_lt hptr hlen_le hlen_eq
      dsimp only at hpack
      refine SepWP.fold hpack (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by rw [← hx26]; wp_norm_goal,
         by rw [← hx27]; wp_norm_goal,
         by rw [← hx28]; wp_norm_goal,
         by wp_norm_goal,
         by wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_
        (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
      rw [houtKey_eq]
      sep_frame

/-! ## Loop of `KeyHistory::get` at `+740` (`0x60bb4`) -/

set_option maxHeartbeats 800000 in
theorem recvKey_get_loop_zero {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (i : Nat) (hi_eq : i = (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 740#64)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  subst hi_eq
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_err880 := @recvKey_err_keyAlreadyRequested_from_880 img hkdf A ext x s0 c3 R
  clear hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr, recv]
  clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hadd36 : (BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length - 36#64) + 36#64 =
      BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by bv_omega
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx9
  wp_norm_hyp hx11
  wp_norm_hyp hx19
  wp_norm_hyp hw20
  wp_norm_hyp hadd36
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 880#64) hF ?_
  wp_steps
  have hpack := chainOuterRecvAt_pack_unchanged A x epochIndex hi_ep gce
    hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
  dsimp only at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by wp_norm_goal⟩
  have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)) := by
    rw [hres, getLoop_of_ge _ _ _ _ _ (Nat.lt_irrefl _)]; rfl
  refine SepWPp.mono_pre _ ?_
    (h_err880 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  sep_frame

set_option maxHeartbeats 800000 in
theorem recvKey_get_loop_step {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hi_mod : i % 36 = 0)
    (h_ih :
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyStateInv img s0 s →
        s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 740#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have hprops := get_loop_idx_props hi36 hbs_lt
  have hadd40 : BitVec.ofNat 64 i + 4#64 = BitVec.ofNat 64 (i + 4) := by bv_omega
  have hneq_len := hprops.2.2.1
  have hult_i4 := hprops.2.2.2.1
  clear hprops
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_hit := @recvKey_get_hit_from_788 img hkdf A ext hshim halloc x s0 c3 R
    epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr hlen_mod i hi36 hi_mod
  clear hshim halloc hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hsplit4 := pointsToBytes_split_u32_at gce.recv.prev.ptr
    (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega)
  refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx9; wp_norm_hyp hx10; wp_norm_hyp hx11; wp_norm_hyp hx19
  wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hx24
  wp_norm_hyp hadd40; wp_norm_hyp hneq_len; wp_norm_hyp hult_i4
  have hex_len : ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)).length = 4 := by
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  have hcmp_eq :
      (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) =
        (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) := by
    rw [pack32LE_beq_rev32Trunc_iff hex_len x.index, List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
  by_cases hhit : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = true
  · have hbeq_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = true := by
      rw [hcmp_eq, hhit]
    have hbne_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = false := by
      simp only [bne, hbeq_t, Bool.not_true]
    wp_norm_hyp hbeq_t; wp_norm_hyp hbne_f
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 788#64) hF ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26]; wp_norm_goal, by rw [← hx27]; wp_norm_goal, by rw [← hx28]; wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres_hit :
        Chain.recvKey hkdf x.self x.epoch x.index =
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let recv' := { recv with prev := recv.prev.remove i x.self.params }
          let outKey := (recv.prev.data.drop (i + 4)).take 32
          .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey) := by
      rw [hres, getLoop_of_hit _ _ _ _ i (by omega) hhit]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_hit hres_hit _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhit_f : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = false :=
      Bool.eq_false_iff.mpr hhit
    have hbeq_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = false := by
      rw [hcmp_eq, hhit_f]
    have hbne_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = true := by
      simp only [bne, hbeq_f, Bool.not_false]
    wp_norm_hyp hbeq_f; wp_norm_hyp hbne_t
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 740#64) hF ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by rw [← hx26]; wp_norm_goal, by rw [← hx27]; wp_norm_goal, by rw [← hx28]; wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres_miss :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
          let recv' := { recv with prev := prev' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, getLoop_of_miss _ _ _ _ i (by omega) hhit_f]; rfl
    have hptr_i_next : gce.recv.prev.ptr + BitVec.ofNat 64 i =
        gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    have hi_next : BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    refine SepWPp.mono_pre _ ?_
      (h_ih hres_miss _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hptr_i_next]; wp_norm_goal) (by rw [← hi_next]; wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

theorem recvKey_get_loop {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (k : Nat) :
    ∀ (i : Nat),
      i ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
      i % 36 = 0 →
      ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length - i) / 36 = k →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyStateInv img s0 s →
        s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R) := by
  induction k with
  | zero =>
    intro i hi_le hi_mod hk hres s hinv hpc _ hx9 _ hx11 hx19 hw20 _ _ _
    exact recvKey_get_loop_zero x s0 c3 epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
      i (by omega) hres s hinv hpc hx9 hx11 hx19 hw20
  | succ k ih =>
    intro i hi_le hi_mod hk hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24
    have hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    exact recvKey_get_loop_step hshim halloc x s0 c3 epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr hlen_mod
      i hi36 hi_mod (ih (i + 36) hi36 (by omega) (by omega))
      hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24

/-! ## Entry of `KeyHistory::get` at `+276` (`0x609e4`) -/

theorem get_entry_div36_props {len : Nat} (hlen_lt : len < 2 ^ 63) :
    let x := BitVec.ofNat 64 len
    let q := (BitVec.truncate 64
      ((BitVec.zeroExtend 128 x * BitVec.zeroExtend 128 0xe38e38e38e38e38f#64) >>> 64)) >>> 5
    (q + (q <<< 3)) <<< 2 = BitVec.ofNat 64 (len / 36 * 36) ∧
    BitVec.ofNat 64 len - BitVec.ofNat 64 (len / 36 * 36) = BitVec.ofNat 64 (len % 36) ∧
    (BitVec.ofNat 64 len == BitVec.ofNat 64 (len / 36 * 36)) = decide (len % 36 = 0) ∧
    (BitVec.ofNat 64 len != BitVec.ofNat 64 (len / 36 * 36)) = !decide (len % 36 = 0) ∧
    (BitVec.ofNat 64 (len % 36) == 0#64) = decide (len % 36 = 0) := by
  intro x q
  have hx_toNat : x.toNat = len := by
    dsimp [x]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmul := mul36_div36_eq x
  dsimp only at hmul
  rw [hx_toNat] at hmul
  have hbeq : (BitVec.ofNat 64 len == BitVec.ofNat 64 (len / 36 * 36)) = decide (len % 36 = 0) := by
    by_cases h : len % 36 = 0
    · have heq : len / 36 * 36 = len := by omega
      simp [h, heq]
    · simp only [h, decide_false, beq_eq_false_iff_ne]
      intro heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : len / 36 * 36 < 2 ^ 64)] at this
      omega
  refine ⟨hmul, ?_, hbeq, by simp [bne, hbeq], ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : len / 36 * 36 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : len % 36 < 2 ^ 64)]
      omega
    · rw [BitVec.le_def]
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : len < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : len / 36 * 36 < 2 ^ 64)]
      omega
  · by_cases h : len % 36 = 0
    · simp [h]
    · simp only [h, decide_false, beq_eq_false_iff_ne]
      intro heq
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : len % 36 < 2 ^ 64)] at this
      omega

theorem get_entry_ovf_props (atIdx ctr : BitVec 32) (params : ChainParamsPB) :
    let maxOoo := params.maxOooKeysOrDefault
    maxOoo + atIdx = atIdx + maxOoo ∧
    (maxOoo.toNat + atIdx.toNat ≥ 2 ^ 32 ↔ atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.uaddOverflow maxOoo atIdx = decide (atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (atIdx + maxOoo) maxOoo = decide (atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (atIdx + maxOoo) atIdx = decide (atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32) ∧
    BitVec.ult (atIdx + maxOoo) ctr = decide (atIdx + maxOoo < ctr) ∧
    BitVec.ule ctr (atIdx + maxOoo) = !decide (atIdx + maxOoo < ctr) := by
  intro maxOoo
  have ha := atIdx.isLt
  have hm := maxOoo.isLt
  refine ⟨BitVec.add_comm _ _, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BitVec.uaddOverflow]
    by_cases h : atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  · by_cases h : atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32
    · rw [decide_eq_true h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega : atIdx.toNat + maxOoo.toNat - 2 ^ 32 < 2 ^ 32)]
      exact decide_eq_true (by omega)
    · rw [decide_eq_false h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
  · by_cases h : atIdx.toNat + maxOoo.toNat ≥ 2 ^ 32
    · rw [decide_eq_true h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega : atIdx.toNat + maxOoo.toNat - 2 ^ 32 < 2 ^ 32)]
      exact decide_eq_true (by omega)
    · rw [decide_eq_false h]
      simp only [BitVec.ult, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact decide_eq_false (by omega)
  · rw [BitVec.ult_eq_decide]
    by_cases h : atIdx + maxOoo < ctr
    · rw [decide_eq_true h, decide_eq_true (BitVec.lt_def.mp h)]
    · rw [decide_eq_false h, decide_eq_false (fun h' => h (BitVec.lt_def.mpr h'))]
  · rw [BitVec.ule_eq_decide]
    by_cases h : atIdx + maxOoo < ctr
    · have h' := BitVec.lt_def.mp h
      rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · have h' : ¬ (atIdx + maxOoo).toNat < ctr.toNat := fun hlt => h (BitVec.lt_def.mpr hlt)
      rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

set_option maxHeartbeats 800000 in
theorem recvKey_get_from_276 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 276#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = (x.self.links[epochIndex]'hi_ep).recv.ctr)
    (hw10 : (s.readReg64 (.gpr 10#5)).setWidth 32 = x.self.params.maxOooKeys)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        vecU8At A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_panic_assert := panic_at_assert_recvKey img.base ext
  have h_panic_add := panic_at_add_ovf_recvKey img.base ext
  have h_err884 := @recvKey_err_keyTrimmed_from_884 img hkdf A ext x s0 c3 R
  have h_loop := @recvKey_get_loop img hkdf A ext hshim halloc x s0 c3 R
    epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
  clear hshim halloc hfn
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  dsimp only [s_idx, epPtr, recv]
  clear s_idx epPtr recv
  have hunpack := vecU8At_unpack A
    (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
    gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data
  have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
  have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack
  clear ha58 ha60
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hp_le, hp_cap, hp_ptr⟩
  refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u64 s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u_sp8
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hmul36, hsub36, hbeq_div36, hbne_div36, hbeq_mod36⟩ := get_entry_div36_props hbs_lt
  have hmaxOoo := maxOooKeysOrDefault_eq_ite x.self.params
  have ⟨hadd_comm, hovf_iff, huadd_ovf, hult_ovf1, hult_ovf2, hult_trim, hule_trim⟩ :=
    get_entry_ovf_props x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hw8
  wp_norm_hyp hw10
  wp_norm_hyp hx19
  wp_norm_hyp hw20
  wp_norm_hyp hx22
  wp_norm_hyp htrace
  wp_norm_hyp hmul36
  wp_norm_hyp hsub36
  wp_norm_hyp hbeq_div36
  wp_norm_hyp hbne_div36
  wp_norm_hyp hbeq_mod36
  wp_norm_hyp hmaxOoo
  wp_norm_hyp hadd_comm
  wp_norm_hyp huadd_ovf
  wp_norm_hyp hult_ovf1
  wp_norm_hyp hult_ovf2
  wp_norm_hyp hult_trim
  wp_norm_hyp hule_trim
  by_cases hmod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0
  · have hmod_t : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = true := decide_eq_true hmod
    have hdiv_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36 * 36 =
        (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    wp_norm_hyp hmod_t
    by_cases hovf : x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
    · have hovf_t : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = true :=
        decide_eq_true hovf
      wp_norm_hyp hovf_t
      apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "core::panicking::panic_const::panic_const_add_overflow" - 0x5b4d8))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_add) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_get_addOverflow _ _ _ _ hmod hovf]; rfl
      exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have hovf_f : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = false :=
        decide_eq_false hovf
      wp_norm_hyp hovf_f
      by_cases htrim : x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr
      · have htrim_t : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = true :=
          decide_eq_true htrim
        wp_norm_hyp htrim_t
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 884#64) hF ?_
        wp_steps
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        have hpack := chainOuterRecvAt_pack_unchanged A x epochIndex hi_ep gce
          hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
        dsimp only at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by rw [← hx26]; wp_norm_goal,
           by rw [← hx27]; wp_norm_goal,
           by rw [← hx28]; wp_norm_goal,
           htrace,
           by wp_norm_goal⟩
        have hres_trim : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)) := by
          rw [hres, keyHistory_get_trimmed _ _ _ _ hmod hovf htrim]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_err884 hres_trim _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · have htrim_f : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = false :=
          decide_eq_false htrim
        wp_norm_hyp htrim_f
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 740#64) hF ?_
        wp_steps
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by rw [← hx26]; wp_norm_goal,
           by rw [← hx27]; wp_norm_goal,
           by rw [← hx28]; wp_norm_goal,
           htrace,
           by wp_norm_goal⟩
        have hres_loop :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params 0
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, keyHistory_get_loop _ _ _ _ hmod hovf htrim]
        have hptr0 : gce.recv.prev.ptr - 36#64 = gce.recv.prev.ptr + BitVec.ofNat 64 0 - 36#64 := by
          simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        refine SepWPp.mono_pre _ ?_
          (h_loop hp_le hp_cap hp_ptr hmod ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36) 0 (Nat.zero_le _) (Nat.zero_mod _) rfl hres_loop _ hinv'
            (by wp_norm_goal) (by wp_norm_goal)
            (by rw [← hdiv_eq]; wp_norm_goal)
            (by rw [← hptr0]; wp_norm_goal)
            (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
  · have hmod_f : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = false := decide_eq_false hmod
    wp_norm_hyp hmod_f
    apply SepWPp.of_sepWP (mid := entry_addr + bv% (ls_off% "core::panicking::assert_failed::<usize, usize>" - 0x5b4d8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using h_panic_assert) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, keyHistory_get_unaligned _ _ _ _ hmod]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm

/-! ## Relocatable `[LibsignalPlacement]` `KeyHistory::get` Proofs (`blkPC_366`) -/

set_option maxHeartbeats 800000 in
theorem recvKey_get_hit_from_788_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hi_mod : i % 36 = 0)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index =
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let recv' := { recv with prev := recv.prev.remove i x.self.params }
      let outKey := (recv.prev.data.drop (i + 4)).take 32
      .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 788#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr)
    (hx25 : s.readReg64 (.gpr 25#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have h_ok708 := @recvKey_ok_from_708_placed _ hkdf A H x s0 c3 R
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨_, _, _, _, hi_add36, hult_i36, hult_i⟩ := get_loop_idx_props hi36 hbs_lt
  have ⟨hule_swap, hswap_lt⟩ := get_swap_idx_props hi36 hbs_lt
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx19; wp_norm_hyp hx21
  wp_norm_hyp hx22; wp_norm_hyp hx23; wp_norm_hyp hx24; wp_norm_hyp hx25; wp_norm_hyp htrace
  wp_norm_hyp hi_add36; wp_norm_hyp hult_i36; wp_norm_hyp hult_i
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 816#64) hF ?_
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
  wp_steps
  have hstack_s0 : stackAt (s0.sp - 128#64) nextKeyInternalStackX = stackAt s.sp nextKeyInternalStackX := by rw [hsp]
  refine SepWP.fold (Entails.of_eq (hstack_s0.trans (stackAt_nextKeyInternalX_top_split s.sp))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  apply SepWP.seq_cps (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
  wp_call hshim ()
  wp_steps
  have hstack_sf : stackAt s.sp extHookStack = stackAt sf.sp extHookStack :=
    congrArg (stackAt · extHookStack) (by wp_norm_goal)
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hinv4
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    wp_norm_hyp hoom_64
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    intro htrace_oom; wp_norm_hyp htrace_oom; wp_norm_hyp hpost
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hoom_ext) fun hm => ?_
    exact allowPanic_recvKey_oom
      (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace_oom, hpost, htrace])) hm
  · have hoom_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hmod1, htrace1⟩; wp_norm_hyp htrace1
    let p_key := sf_1.readReg64 (Reg.gpr 0#5)
    have hstack_back :
        memRegion (s.sp - BitVec.ofNat 64 nextKeyInternalStackX) 176 ∗ stackAt sf.sp extHookStack =
          stackAt (s0.sp - 128#64) nextKeyInternalStackX := by
      rw [hsp_sf, ← stackAt_nextKeyInternalX_top_split s.sp, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    refine SepWPp.fold (Entails.of_eq (ChainNewFacts.memRegion_32_cells4 p_key)) (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro u0; apply SepWPp.exists_elim; intro u1
    apply SepWPp.exists_elim; intro u2; apply SepWPp.exists_elim; intro u3
    obtain ⟨k0, k1, k2, k3, hget_cells⟩ :=
      exists_entry36_get_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i hi36
    have ⟨hbs_get, hkey_pack⟩ := hget_cells gce.recv.prev.ptr
    refine SepWPp.fold (Entails.of_eq hbs_get) (by sep_focus) ?_
    have hsp_sf1 : sf_1.sp = s0.sp - 128#64 := by rw [hsp_sf_1, hsp_sf, hsp]
    have hsp1_align : sf_1.spAligned = true := by
      simp only [State.spAligned, hsp_sf1] at hsp0_align ⊢; revert hsp0_align; bv_kernel
    wp_norm_hyp hsp_sf1; wp_norm_hyp hsp1_align; wp_norm_hyp hule_swap
    let outKey := ((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop (i + 4)).take 32
    have houtKey_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.extract (i + 4) (i + 36) = outKey := by
      rw [List.extract_eq_take_drop, show i + 36 - (i + 4) = 32 by omega]
    have houtKey_len : outKey.length = 32 := by
      rw [← houtKey_eq]; simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
    by_cases hlt_end : i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length
    · have hule_f : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = false :=
        decide_eq_false (not_not.mpr hlt_end)
      have ⟨hsub36, hult_sub36⟩ := hswap_lt hlt_end
      wp_norm_hyp hule_f; wp_norm_hyp hsub36; wp_norm_hyp hult_sub36
      obtain ⟨ei0, ei1, ei2, ei3, ei4, el0, el1, el2, el3, el4, hswap_cells⟩ :=
        exists_entry36_swap_cells (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega) (by omega)
      have ⟨hbs_swap_in, hbs_swap_out⟩ := hswap_cells gce.recv.prev.ptr
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hinv4 ?_
      apply SepWP.seq_cps (mid := (blkPl_366).base + 840#64)
      wp_steps
      refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_swap_in) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      wp_steps
      refine SepWP.fold (Entails.of_eq hbs_swap_out) (by sep_focus) ?_
      have hrem := vecU8At_pack_remove_swap A
        (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
        gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params hlt_end hp_le hp_cap hp_ptr
      dsimp only [KeyHistory.KEY_SIZE] at hrem
      have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
      have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
      rw [ha58, ha60] at hrem
      refine SepWP.fold hrem (by sep_focus) ?_
      have hpack := chainOuterRecvAt_pack A x epochIndex hi_ep gce gce.recv.prev
        { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
        hhead hcap_lt hptr hlen_le hlen_eq
      dsimp only at hpack
      refine SepWP.fold hpack (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
         (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal)⟩
      refine SepWPp.mono_pre _ ?_
        (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
      rw [houtKey_eq]; sep_frame
    · have hule_t : decide (¬ (i + 36 < (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)) = true :=
        decide_eq_true hlt_end
      wp_norm_hyp hule_t
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 708#64) hinv4 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hkey_pack p_key)) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq hbs_get.symm) (by sep_focus) ?_
      have hrem := vecU8At_pack_remove_last A
        (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
        gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data i x.self.params (by omega) hlt_end hp_le hp_cap hp_ptr
      have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
      have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
      rw [ha58, ha60] at hrem
      refine SepWP.fold hrem (by sep_focus) ?_
      have hpack := chainOuterRecvAt_pack A x epochIndex hi_ep gce gce.recv.prev
        { (x.self.links[epochIndex]'hi_ep).recv with prev := (x.self.links[epochIndex]'hi_ep).recv.prev.remove i x.self.params }
        hhead hcap_lt hptr hlen_le hlen_eq
      dsimp only at hpack
      refine SepWP.fold hpack (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
         (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), (by wp_norm_goal), (by wp_norm_goal)⟩
      refine SepWPp.mono_pre _ ?_
        (h_ok708 _ outKey p_key hoom_64 houtKey_len hres _ hinv'
          (by wp_norm_goal) (by dsimp only [p_key]; wp_norm_goal) (by wp_norm_goal))
      rw [houtKey_eq]; sep_frame

set_option maxHeartbeats 800000 in
theorem recvKey_get_loop_zero_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (i : Nat) (hi_eq : i = (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 740#64)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv; subst hi_eq
  have h_err880 := @recvKey_err_keyAlreadyRequested_from_880_placed _ hkdf A H x s0 c3 R
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hadd36 : (BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length - 36#64) + 36#64 =
      BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by bv_omega
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx9; wp_norm_hyp hx11
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hadd36
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 880#64) hF ?_
  wp_steps
  have hpack := chainOuterRecvAt_pack_unchanged A x epochIndex hi_ep gce
    hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
  dsimp only at hpack
  refine SepWP.fold hpack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal)⟩
  have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)) := by
    rw [hres, getLoop_of_ge _ _ _ _ _ (Nat.lt_irrefl _)]; rfl
  refine SepWPp.mono_pre _ ?_
    (h_err880 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
  sep_frame

set_option maxHeartbeats 800000 in
theorem recvKey_get_loop_step_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (i : Nat) (hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hi_mod : i % 36 = 0)
    (h_ih :
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyPlacedStateInv lsmpl s0 s →
        s.pc = (blkPl_366).base + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 (i + 36) - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R))
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 740#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index)
    (hx9 : s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx10 : s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64)
    (hx11 : s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112))
    (hx24 : s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have hprops := get_loop_idx_props hi36 hbs_lt
  have hadd40 : BitVec.ofNat 64 i + 4#64 = BitVec.ofNat 64 (i + 4) := by bv_omega
  have hneq_len := hprops.2.2.1; have hult_i4 := hprops.2.2.2.1; clear hprops
  have h_hit := @recvKey_get_hit_from_788_placed _ hkdf A H hshim halloc hoom_ext x s0 c3 R
    epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr hlen_mod i hi36 hi_mod
  clear hshim halloc hoom_ext
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hsplit4 := pointsToBytes_split_u32_at gce.recv.prev.ptr
    (x.self.links[epochIndex]'hi_ep).recv.prev.data i (by omega)
  refine SepWPp.fold (Entails.of_eq hsplit4) (by sep_focus) ?_
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8
  wp_norm_hyp hx9; wp_norm_hyp hx10; wp_norm_hyp hx11; wp_norm_hyp hx19
  wp_norm_hyp hw20; wp_norm_hyp hx21; wp_norm_hyp hx22; wp_norm_hyp hx24
  wp_norm_hyp hadd40; wp_norm_hyp hneq_len; wp_norm_hyp hult_i4
  have hex_len : ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)).length = 4 := by
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  have hcmp_eq :
      (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) =
        (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) := by
    rw [pack32LE_beq_rev32Trunc_iff hex_len x.index, List.extract_eq_take_drop, show i + 4 - i = 4 by omega]
  by_cases hhit : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = true
  · have hbeq_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = true := by
      rw [hcmp_eq, hhit]
    have hbne_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = false := by
      simp only [bne, hbeq_t, Bool.not_true]
    wp_norm_hyp hbeq_t; wp_norm_hyp hbne_f
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 788#64) hF ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal)⟩
    have hres_hit :
        Chain.recvKey hkdf x.self x.epoch x.index =
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let recv' := { recv with prev := recv.prev.remove i x.self.params }
          let outKey := (recv.prev.data.drop (i + 4)).take 32
          .ok ({ x.self with links := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' } }, outKey) := by
      rw [hres, getLoop_of_hit _ _ _ _ i (by omega) hhit]; rfl
    refine SepWPp.mono_pre _ ?_
      (h_hit hres_hit _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have hhit_f : (((x.self.links[epochIndex]'hi_ep).recv.prev.data.drop i).take 4 == toBEBytes 4 x.index) = false :=
      Bool.eq_false_iff.mpr hhit
    have hbeq_f : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) == rev32Trunc x.index) = false := by
      rw [hcmp_eq, hhit_f]
    have hbne_t : (pack32LE ((x.self.links[epochIndex]'hi_ep).recv.prev.data.extract i (i + 4)) != rev32Trunc x.index) = true := by
      simp only [bne, hbeq_f, Bool.not_false]
    wp_norm_hyp hbeq_f; wp_norm_hyp hbne_t
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 740#64) hF ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq hsplit4.symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
       (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal)⟩
    have hres_miss :
        Chain.recvKey hkdf x.self x.epoch x.index = (do
          let recv := (x.self.links[epochIndex]'hi_ep).recv
          let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params (i + 36)
          let recv' := { recv with prev := prev' }
          let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
          return ({ x.self with links := links' }, outKey)) := by
      rw [hres, getLoop_of_miss _ _ _ _ i (by omega) hhit_f]; rfl
    have hptr_i_next : gce.recv.prev.ptr + BitVec.ofNat 64 i =
        gce.recv.prev.ptr + BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    have hi_next : BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 36) - 36#64 := by bv_omega
    refine SepWPp.mono_pre _ ?_
      (h_ih hres_miss _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by rw [← hptr_i_next]; wp_norm_goal) (by rw [← hi_next]; wp_norm_goal)
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

theorem recvKey_get_loop_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hp_le : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length ≤ gce.recv.prev.cap.toNat)
    (hp_cap : gce.recv.prev.cap.toNat < 2 ^ 63)
    (hp_ptr : gce.recv.prev.ptr ≠ 0)
    (hlen_mod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0)
    (k : Nat) :
    ∀ (i : Nat),
      i ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
      i % 36 = 0 →
      ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length - i) / 36 = k →
      (Chain.recvKey hkdf x.self x.epoch x.index = (do
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params i
        let recv' := { recv with prev := prev' }
        let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
        return ({ x.self with links := links' }, outKey))) →
      ∀ (s : State), RecvKeyPlacedStateInv lsmpl s0 s →
        s.pc = (blkPl_366).base + 740#64 →
        (s.readReg64 (.gpr 8#5)).setWidth 32 = rev32Trunc x.index →
        s.readReg64 (.gpr 9#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 10#5) = gce.recv.prev.ptr + BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 i - 36#64 →
        s.readReg64 (.gpr 19#5) = x.out →
        (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index →
        s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (x.self.links[epochIndex]'hi_ep).recv.prev.data.length →
        s.readReg64 (.gpr 22#5) =
          x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) →
        s.readReg64 (.gpr 24#5) = gce.recv.prev.ptr →
        let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
        let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
        let recv := (x.self.links[epochIndex]'hi_ep).recv
        SepWPp ((blkPC_366).rebase (blkPl_366).base H)
          (s0.readReg64 (.gpr 30#5)) s
          (memRegion x.out 32 ∗
            chainOuterRecvAt A x epochIndex hi_ep gce ∗
            vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
            ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
            ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
            ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 recv.prev.data.length) ∗
            (gce.recv.prev.ptr ↦ₛ recv.prev.data) ∗
            vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data.length ∗
            ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
            memRegion (epPtr + 0x6c#64) 4 ∗
            stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
            memRegion (s0.sp - 120#64) 36 ∗
            recvKeyFrameRestAt s0 c3 ∗
            A.pool)
          (recvKeyPost hkdf A x s0)
          (recvKeyPanic hkdf A x s0 R) := by
  induction k with
  | zero =>
    intro i hi_le hi_mod hk hres s hinv hpc _ hx9 _ hx11 hx19 hw20 _ _ _
    exact recvKey_get_loop_zero_placed x s0 c3 epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
      i (by omega) hres s hinv hpc hx9 hx11 hx19 hw20
  | succ k ih =>
    intro i hi_le hi_mod hk hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24
    have hi36 : i + 36 ≤ (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    exact recvKey_get_loop_step_placed hshim halloc hoom_ext x s0 c3 epochIndex hi_ep gce
      hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr hlen_mod
      i hi36 hi_mod (ih (i + 36) hi36 (by omega) (by omega))
      hres s hinv hpc hw8 hx9 hx10 hx11 hx19 hw20 hx21 hx22 hx24

set_option maxHeartbeats 800000 in
theorem recvKey_get_from_276_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (epochIndex : Nat) (hi_ep : epochIndex < x.self.links.length)
    (gce : ChainEpochGhost)
    (hhead : x.G.linksHead.toNat < x.G.linksCap.toNat)
    (hcap_lt : x.G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : x.G.linksPtr ≠ 0#64)
    (hlen_le : x.self.links.length ≤ x.G.linksCap.toNat)
    (hlen_eq : x.G.epochs.length = x.self.links.length)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = (do
      let recv := (x.self.links[epochIndex]'hi_ep).recv
      let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
      let recv' := { recv with prev := prev' }
      let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
      return ({ x.self with links := links' }, outKey)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 276#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = (x.self.links[epochIndex]'hi_ep).recv.ctr)
    (hw10 : (s.readReg64 (.gpr 10#5)).setWidth 32 = x.self.params.maxOooKeys)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index)
    (hx22 : s.readReg64 (.gpr 22#5) =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112)) :
    let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
    let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
    let recv := (x.self.links[epochIndex]'hi_ep).recv
    SepWPp ((blkPC_366).rebase (blkPl_366).base H)
      (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainOuterRecvAt A x epochIndex hi_ep gce ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv.next ∗
        vecU8At A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr recv.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro s_idx epPtr recv
  have h_err884 := @recvKey_err_keyTrimmed_from_884_placed _ hkdf A H x s0 c3 R
  have h_loop := @recvKey_get_loop_placed _ hkdf A H hshim halloc hoom_ext x s0 c3 R
    epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
  clear hshim halloc hoom_ext
  dsimp only [s_idx, epPtr, recv]; clear s_idx epPtr recv
  have hunpack := vecU8At_unpack A
    (x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64)
    gce.recv.prev.cap gce.recv.prev.ptr (x.self.links[epochIndex]'hi_ep).recv.prev.data
  have ha58 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 8#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x58#64 := by bv_kernel
  have ha60 : x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x50#64 + 16#64 =
      x.G.linksPtr + BitVec.ofNat 64 (vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex * 112) + 0x60#64 := by bv_kernel
  rw [ha58, ha60] at hunpack; clear ha58 ha60
  refine SepWPp.fold hunpack (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hp_le, hp_cap, hp_ptr⟩
  refine SepWPp.fold (Entails.of_eq (memRegion_36_split_u64 s0.sp)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro u_sp8
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hvregs
  have hbs_lt : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp_le hp_cap
  have ⟨hmul36, hsub36, hbeq_div36, hbne_div36, hbeq_mod36⟩ := get_entry_div36_props hbs_lt
  have hmaxOoo := maxOooKeysOrDefault_eq_ite x.self.params
  have ⟨hadd_comm, hovf_iff, huadd_ovf, hult_ovf1, hult_ovf2, hult_trim, hule_trim⟩ :=
    get_entry_ovf_props x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hw10
  wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp hx22; wp_norm_hyp htrace
  wp_norm_hyp hmul36; wp_norm_hyp hsub36; wp_norm_hyp hbeq_div36; wp_norm_hyp hbne_div36
  wp_norm_hyp hbeq_mod36; wp_norm_hyp hmaxOoo; wp_norm_hyp hadd_comm; wp_norm_hyp huadd_ovf
  wp_norm_hyp hult_ovf1; wp_norm_hyp hult_ovf2; wp_norm_hyp hult_trim; wp_norm_hyp hule_trim
  by_cases hmod : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0
  · have hmod_t : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = true := decide_eq_true hmod
    have hdiv_eq : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36 * 36 =
        (x.self.links[epochIndex]'hi_ep).recv.prev.data.length := by omega
    wp_norm_hyp hmod_t
    by_cases hovf : x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32
    · have hovf_t : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = true :=
        decide_eq_true hovf
      wp_norm_hyp hovf_t
      apply SepWPp.of_sepWP (mid := lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow")
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hadd_ext) fun hm => ?_
      have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
        rw [hres, keyHistory_get_addOverflow _ _ _ _ hmod hovf]; rfl
      exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm
    · have hovf_f : decide (x.index.toNat + x.self.params.maxOooKeysOrDefault.toNat ≥ 2 ^ 32) = false :=
        decide_eq_false hovf
      wp_norm_hyp hovf_f
      by_cases htrim : x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr
      · have htrim_t : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = true :=
          decide_eq_true htrim
        wp_norm_hyp htrim_t
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 884#64) hF ?_
        wp_steps
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        have hpack := chainOuterRecvAt_pack_unchanged A x epochIndex hi_ep gce
          hhead hcap_lt hptr hlen_le hlen_eq hp_le hp_cap hp_ptr
        dsimp only at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
           (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hres_trim : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)) := by
          rw [hres, keyHistory_get_trimmed _ _ _ _ hmod hovf htrim]; rfl
        refine SepWPp.mono_pre _ ?_
          (h_err884 hres_trim _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · have htrim_f : decide (x.index + x.self.params.maxOooKeysOrDefault < (x.self.links[epochIndex]'hi_ep).recv.ctr) = false :=
          decide_eq_false htrim
        wp_norm_hyp htrim_f
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 740#64) hF ?_
        wp_steps
        refine SepWP.fold (pointsTo64_memRegion_28_entails_36 s0.sp _) (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
           (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by wp_norm_goal)⟩
        have hres_loop :
            Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← KeyHistory.getLoop recv.prev x.index (toBEBytes 4 x.index) x.self.params 0
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
          rw [hres, keyHistory_get_loop _ _ _ _ hmod hovf htrim]
        have hptr0 : gce.recv.prev.ptr - 36#64 = gce.recv.prev.ptr + BitVec.ofNat 64 0 - 36#64 := by
          simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
        refine SepWPp.mono_pre _ ?_
          (h_loop hp_le hp_cap hp_ptr hmod ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length / 36) 0 (Nat.zero_le _) (Nat.zero_mod _) rfl hres_loop _ hinv'
            (by wp_norm_goal) (by wp_norm_goal)
            (by rw [← hdiv_eq]; wp_norm_goal)
            (by rw [← hptr0]; wp_norm_goal)
            (by wp_norm_goal)
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
  · have hmod_f : decide ((x.self.links[epochIndex]'hi_ep).recv.prev.data.length % 36 = 0) = false := decide_eq_false hmod
    wp_norm_hyp hmod_f
    apply SepWPp.of_sepWP (mid := lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hassert_ext) fun hm => ?_
    have hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true := by
      rw [hres, keyHistory_get_unaligned _ _ _ _ hmod]; rfl
    exact allowPanic_recvKey_panic hpan (by simp only [Rust.panicked, arm64_norm, htrace]) hm

end CryptoVerification.SpqrV1.ChainProofs
