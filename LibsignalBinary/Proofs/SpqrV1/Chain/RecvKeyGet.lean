/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpers
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpers
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Frame, Unpack/Pack, and Return-Tail Helpers for `<spqr::chain::Chain>::recv_key`

Byte-slice 36-byte entry extraction, stack frame splitting, `chainEpochAt` unpack/pack bridges,
and epilogue / `Ok` / `Err` return-tail lemmas (`+248`, `+708`, `+884`, `+880`, `+204`, `+228`)
for `<spqr::chain::Chain>::recv_key` (`0x608d0`, Block `366`).
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

namespace RecvKeyDecodes
gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x5b4d8 → 0x5b9b8]
end RecvKeyDecodes
open RecvKeyDecodes

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## Callee Offsets, Byte-Slice, Stack, and `chainEpochAt` Helpers -/

abbrev sliceIndexFailSymName : String := "core::slice::index::slice_index_fail"
abbrev panicSubOverflowSymName : String := "core::panicking::panic_const::panic_const_sub_overflow"
abbrev expectFailedSymName : String := "core::option::expect_failed"

theorem chainRecvKey_fnOff : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x5b4d8

theorem doReserve7_fnOff : libsignalSessionCode.fnOff doReserve7Name = 0x4dca8 :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) libsignalSessionCode_fnOff_0x4dca8

theorem sliceIndexFail_fnOff : libsignalSessionCode.fnOff sliceIndexFailSymName =
    num% (ls_off% "core::slice::index::slice_index_fail") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "core::slice::index::slice_index_fail")

theorem panicSubOverflow_fnOff : libsignalSessionCode.fnOff panicSubOverflowSymName =
    num% (ls_off% "core::panicking::panic_const::panic_const_sub_overflow") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_stub% "core::panicking::panic_const::panic_const_sub_overflow")

theorem expectFailed_fnOff : libsignalSessionCode.fnOff expectFailedSymName =
    num% (ls_off% "core::option::expect_failed") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_stub% "core::option::expect_failed")

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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

/-- Decompose any 32-byte list into four 64-bit little-endian words. -/
theorem exists_cells4_of_length_32 {bs : Bytes} (hlen : bs.length = 32) :
    ∃ k0 k1 k2 k3 : BitVec 64,
      ∀ p : BitVec 64,
        (p ↦ₛ bs) =
          (p ↦₆₄ k0) ∗ ((p + 8#64) ↦₆₄ k1) ∗ ((p + 16#64) ↦₆₄ k2) ∗ ((p + 24#64) ↦₆₄ k3) := by
  obtain ⟨k0, k1, k2, k3, _, hp⟩ := exists_unpack64_of_length_32 hlen
  exact ⟨k0, k1, k2, k3, hp⟩

/-- Split `ptr ↦ₛ bs` around a 4-byte u32 at offset `i` (`i + 4 ≤ bs.length`). -/
theorem pointsToBytes_split_u32_at (ptr : BitVec 64) (bs : Bytes) (i : Nat)
    (hi4 : i + 4 ≤ bs.length) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ bs.take i) ∗
      ((ptr + BitVec.ofNat 64 i) ↦₃₂ pack32LE (bs.extract i (i + 4))) ∗
      ((ptr + BitVec.ofNat 64 (i + 4)) ↦ₛ bs.drop (i + 4)) := by
  have hdrop : bs.drop (i + 4) = (bs.drop i).drop 4 := by
    rw [List.drop_drop, Nat.add_comm]
  have hbs : bs = bs.take i ++ (bs.extract i (i + 4) ++ bs.drop (i + 4)) := by
    rw [List.extract_eq_take_drop, show i + 4 - i = 4 by omega, hdrop,
      List.take_append_drop, List.take_append_drop]
  have hlen_i : (bs.take i).length = i := List.length_take_of_le (by omega)
  have hlen_4 : (bs.extract i (i + 4)).length = 4 := by
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, hlen_i, hlen_4,
    pointsTo32_eq_pointsToBytes, unpack32_pack32LE hlen_4]
  have haddr : ptr + BitVec.ofNat 64 i + BitVec.ofNat 64 4 = ptr + BitVec.ofNat 64 (i + 4) := by
    bv_omega
  rw [haddr]

/-- Extract the four 64-bit words of the 32-byte key at `i + 4..i + 36` inside `ptr ↦ₛ bs`. -/
theorem exists_entry36_get_cells (bs : Bytes) (i : Nat) (hi36 : i + 36 ≤ bs.length) :
    ∃ k0 k1 k2 k3 : BitVec 64,
      ∀ p : BitVec 64,
        (p ↦ₛ bs) =
          (p ↦ₛ bs.take (i + 4)) ∗
          ((p + BitVec.ofNat 64 i + 4#64) ↦₆₄ k0) ∗
          ((p + BitVec.ofNat 64 i + 12#64) ↦₆₄ k1) ∗
          ((p + BitVec.ofNat 64 i + 20#64) ↦₆₄ k2) ∗
          ((p + BitVec.ofNat 64 i + 28#64) ↦₆₄ k3) ∗
          ((p + BitVec.ofNat 64 (i + 36)) ↦ₛ bs.drop (i + 36)) ∧
        ∀ q : BitVec 64,
          (q ↦₆₄ k0) ∗ ((q + 8#64) ↦₆₄ k1) ∗ ((q + 16#64) ↦₆₄ k2) ∗ ((q + 24#64) ↦₆₄ k3) =
            (q ↦ₛ bs.extract (i + 4) (i + 36)) := by
  let key := bs.extract (i + 4) (i + 36)
  have hkey_len : key.length = 32 := by
    dsimp [key]; simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  obtain ⟨k0, k1, k2, k3, hkey⟩ := exists_cells4_of_length_32 hkey_len
  refine ⟨k0, k1, k2, k3, fun p => ⟨?_, fun q => (hkey q).symm⟩⟩
  have hdrop : bs.drop (i + 36) = (bs.drop (i + 4)).drop 32 := by
    rw [List.drop_drop, show i + 4 + 32 = i + 36 by omega]
  have hbs : bs = bs.take (i + 4) ++ (key ++ bs.drop (i + 36)) := by
    change bs = bs.take (i + 4) ++ (bs.extract (i + 4) (i + 36) ++ bs.drop (i + 36))
    rw [List.extract_eq_take_drop, show i + 36 - (i + 4) = 32 by omega, hdrop,
      List.take_append_drop, List.take_append_drop]
  have hlen1 : (bs.take (i + 4)).length = i + 4 := List.length_take_of_le (by omega)
  conv_lhs => rw [hbs]
  rw [pointsToBytes_append, pointsToBytes_append, hlen1, hkey_len,
    hkey (p + BitVec.ofNat 64 (i + 4))]
  have ha0 : p + BitVec.ofNat 64 (i + 4) = p + BitVec.ofNat 64 i + 4#64 := by bv_omega
  have ha1 : p + BitVec.ofNat 64 (i + 4) + 8#64 = p + BitVec.ofNat 64 i + 12#64 := by bv_omega
  have ha2 : p + BitVec.ofNat 64 (i + 4) + 16#64 = p + BitVec.ofNat 64 i + 20#64 := by bv_omega
  have ha3 : p + BitVec.ofNat 64 (i + 4) + 24#64 = p + BitVec.ofNat 64 i + 28#64 := by bv_omega
  have ha4 : p + BitVec.ofNat 64 (i + 4) + BitVec.ofNat 64 32 = p + BitVec.ofNat 64 (i + 36) := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha0]
  ac_rfl

/-- Extract the 36-byte entry at `i..i+36` and the last 36-byte entry at `len-36..len`
when `i + 36 ≤ bs.length - 36`. -/
theorem exists_entry36_swap_cells (bs : Bytes) (i : Nat) (hi : i + 36 ≤ bs.length - 36)
    (hlen36 : 36 ≤ bs.length) :
    ∃ (ei0 ei1 ei2 ei3 : BitVec 64) (ei4 : BitVec 32)
      (el0 el1 el2 el3 : BitVec 64) (el4 : BitVec 32),
      ∀ p : BitVec 64,
        (p ↦ₛ bs) =
          (p ↦ₛ bs.take i) ∗
          ((p + BitVec.ofNat 64 i) ↦₆₄ ei0) ∗
          ((p + BitVec.ofNat 64 i + 8#64) ↦₆₄ ei1) ∗
          ((p + BitVec.ofNat 64 i + 16#64) ↦₆₄ ei2) ∗
          ((p + BitVec.ofNat 64 i + 24#64) ↦₆₄ ei3) ∗
          ((p + BitVec.ofNat 64 i + 32#64) ↦₃₂ ei4) ∗
          ((p + BitVec.ofNat 64 (i + 36)) ↦ₛ bs.extract (i + 36) (bs.length - 36)) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36)) ↦₆₄ el0) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 8#64) ↦₆₄ el1) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 16#64) ↦₆₄ el2) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 24#64) ↦₆₄ el3) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 32#64) ↦₃₂ el4) ∧
        (p ↦ₛ bs.take i) ∗
          ((p + BitVec.ofNat 64 i) ↦₆₄ el0) ∗
          ((p + BitVec.ofNat 64 i + 8#64) ↦₆₄ el1) ∗
          ((p + BitVec.ofNat 64 i + 16#64) ↦₆₄ el2) ∗
          ((p + BitVec.ofNat 64 i + 24#64) ↦₆₄ el3) ∗
          ((p + BitVec.ofNat 64 i + 32#64) ↦₃₂ el4) ∗
          ((p + BitVec.ofNat 64 (i + 36)) ↦ₛ bs.extract (i + 36) (bs.length - 36)) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36)) ↦₆₄ el0) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 8#64) ↦₆₄ el1) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 16#64) ↦₆₄ el2) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 24#64) ↦₆₄ el3) ∗
          ((p + BitVec.ofNat 64 (bs.length - 36) + 32#64) ↦₃₂ el4) =
          (p ↦ₛ (bs.take i ++ bs.drop (bs.length - 36) ++ bs.drop (i + 36))) := by
  let ent_i := bs.extract i (i + 36)
  let ent_l := bs.drop (bs.length - 36)
  have hlen_ei : ent_i.length = 36 := by
    dsimp [ent_i]; simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  have hlen_el : ent_l.length = 36 := by
    dsimp [ent_l]; rw [List.length_drop]; omega
  have hli32 : (ent_i.take 32).length = 32 := List.length_take_of_le (by omega)
  have hll32 : (ent_l.take 32).length = 32 := List.length_take_of_le (by omega)
  have hli4 : (ent_i.drop 32).length = 4 := by rw [List.length_drop, hlen_ei]
  have hll4 : (ent_l.drop 32).length = 4 := by rw [List.length_drop, hlen_el]
  obtain ⟨ei0, ei1, ei2, ei3, hei32⟩ := exists_cells4_of_length_32 hli32
  obtain ⟨el0, el1, el2, el3, hel32⟩ := exists_cells4_of_length_32 hll32
  let ei4 : BitVec 32 := pack32LE (ent_i.drop 32)
  let el4 : BitVec 32 := pack32LE (ent_l.drop 32)
  have hent_i_eq : ∀ q : BitVec 64,
      (q ↦ₛ ent_i) =
        (q ↦₆₄ ei0) ∗ ((q + 8#64) ↦₆₄ ei1) ∗ ((q + 16#64) ↦₆₄ ei2) ∗
        ((q + 24#64) ↦₆₄ ei3) ∗ ((q + 32#64) ↦₃₂ ei4) := by
    intro q
    conv_lhs => rw [← List.take_append_drop 32 ent_i]
    rw [pointsToBytes_append, hli32, hei32 q, pointsTo32_eq_pointsToBytes,
      unpack32_pack32LE hli4]
    have hq32 : q + BitVec.ofNat 64 32 = q + 32#64 := rfl
    rw [hq32]; ac_rfl
  have hent_l_eq : ∀ q : BitVec 64,
      (q ↦ₛ ent_l) =
        (q ↦₆₄ el0) ∗ ((q + 8#64) ↦₆₄ el1) ∗ ((q + 16#64) ↦₆₄ el2) ∗
        ((q + 24#64) ↦₆₄ el3) ∗ ((q + 32#64) ↦₃₂ el4) := by
    intro q
    conv_lhs => rw [← List.take_append_drop 32 ent_l]
    rw [pointsToBytes_append, hll32, hel32 q, pointsTo32_eq_pointsToBytes,
      unpack32_pack32LE hll4]
    have hq32 : q + BitVec.ofNat 64 32 = q + 32#64 := rfl
    rw [hq32]; ac_rfl
  have hdrop_mid : bs.drop (bs.length - 36) = (bs.drop (i + 36)).drop (bs.length - 36 - (i + 36)) := by
    rw [List.drop_drop, show i + 36 + (bs.length - 36 - (i + 36)) = bs.length - 36 by omega]
  have hmid_append : bs.extract (i + 36) (bs.length - 36) ++ ent_l = bs.drop (i + 36) := by
    change bs.extract (i + 36) (bs.length - 36) ++ bs.drop (bs.length - 36) = bs.drop (i + 36)
    rw [List.extract_eq_take_drop, hdrop_mid, List.take_append_drop]
  have hlen_ti : (bs.take i).length = i := List.length_take_of_le (by omega)
  have hlen_mid : (bs.extract (i + 36) (bs.length - 36)).length = bs.length - 36 - (i + 36) := by
    simp only [List.extract_eq_take_drop, List.length_take, List.length_drop]; omega
  refine ⟨ei0, ei1, ei2, ei3, ei4, el0, el1, el2, el3, el4, fun p => ⟨?_, ?_⟩⟩
  · have hdrop_i : bs.drop (i + 36) = (bs.drop i).drop 36 := by
      rw [List.drop_drop, Nat.add_comm]
    have hbs : bs = bs.take i ++ (ent_i ++ (bs.extract (i + 36) (bs.length - 36) ++ ent_l)) := by
      rw [hmid_append]
      change bs = bs.take i ++ (bs.extract i (i + 36) ++ bs.drop (i + 36))
      rw [List.extract_eq_take_drop, show i + 36 - i = 36 by omega, hdrop_i,
        List.take_append_drop, List.take_append_drop]
    conv_lhs => rw [hbs]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      hlen_ti, hlen_ei, hlen_mid]
    have ha1 : p + BitVec.ofNat 64 i + BitVec.ofNat 64 36 = p + BitVec.ofNat 64 (i + 36) := by bv_omega
    have ha2 : p + BitVec.ofNat 64 (i + 36) + BitVec.ofNat 64 (bs.length - 36 - (i + 36)) =
        p + BitVec.ofNat 64 (bs.length - 36) := by bv_omega
    rw [ha1, ha2, hent_i_eq (p + BitVec.ofNat 64 i), hent_l_eq (p + BitVec.ofNat 64 (bs.length - 36))]
    ac_rfl
  · have hrhs :
        bs.take i ++ bs.drop (bs.length - 36) ++ bs.drop (i + 36) =
          bs.take i ++ (ent_l ++ (bs.extract (i + 36) (bs.length - 36) ++ ent_l)) := by
      rw [hmid_append, List.append_assoc]
    conv_rhs => rw [hrhs]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      hlen_ti, hlen_el, hlen_mid]
    have ha1 : p + BitVec.ofNat 64 i + BitVec.ofNat 64 36 = p + BitVec.ofNat 64 (i + 36) := by bv_omega
    have ha2 : p + BitVec.ofNat 64 (i + 36) + BitVec.ofNat 64 (bs.length - 36 - (i + 36)) =
        p + BitVec.ofNat 64 (bs.length - 36) := by bv_omega
    rw [ha1, ha2, hent_l_eq (p + BitVec.ofNat 64 i), hent_l_eq (p + BitVec.ofNat 64 (bs.length - 36))]
    ac_rfl

/-- Split `memRegion out 32` for `Error::EpochOutOfRange` (tag 4, `u64` at `+16`). -/
theorem memRegion_32_err_epoch_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      memRegion (out + 9#64) 7 ∗
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      memRegion (out + 24#64) 8 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 24) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 23) (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 7) (k := 16) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 8) (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64)]

/-- Split `memRegion out 32` for `Error::KeyJump` (tag 9, two `u32`s at `+12` and `+16`). -/
theorem memRegion_32_err_jump_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      memRegion (out + 9#64) 3 ∗
      (∃∗ d1 : BitVec 32, (out + 12#64) ↦₃₂ d1) ∗
      (∃∗ d2 : BitVec 32, (out + 16#64) ↦₃₂ d2) ∗
      memRegion (out + 20#64) 12 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 24) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 23) (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20) (b' := out + 12#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 16) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 4) (k := 12) (b' := out + 20#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_four (out + 12#64),
    ProofLib.memRegion_four (out + 16#64)]

/-- Split `memRegion out 32` for `Error::KeyExpired` / `Error::KeyAlreadyRequested`
(tag 10 / 11, one `u32` at `+12`). -/
theorem memRegion_32_err_u32_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ b0 : BitVec 8, (out + 8#64) ↦₈ b0) ∗
      memRegion (out + 9#64) 3 ∗
      (∃∗ d1 : BitVec 32, (out + 12#64) ↦₃₂ d1) ∗
      memRegion (out + 16#64) 16 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 24) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 1) (k := 23) (b' := out + 9#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 9#64) (n := 3) (k := 20) (b' := out + 12#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 12#64) (n := 4) (k := 16) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_one (out + 8#64),
    ProofLib.memRegion_four (out + 12#64)]

/-- Split `memRegion out 32` into four 64-bit cells for the `Ok` return path of `recv_key`. -/
theorem memRegion_32_ok_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w0 : BitVec 64, out ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (out + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (out + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (out + 24#64) ↦₆₄ w3) := by
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 24) (b' := out + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 8#64) (n := 8) (k := 16) (b' := out + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := out + 16#64) (n := 8) (k := 8) (b' := out + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight out,
    ProofLib.memRegion_eight (out + 8#64),
    ProofLib.memRegion_eight (out + 16#64),
    ProofLib.memRegion_eight (out + 24#64)]

/-- Saved callee-saved registers on the `recv_key` stack frame (`sp0 - 80` .. `sp0 - 8`). -/
def calleeSavedRecvKeyAt (sp0 : BitVec 64) (s0 : State) (c3 : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 56#64) ↦₆₄ c3) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Split `stackAt sp chainRecvKeyStackX` (`128 + nextKeyInternalStackX` = `16688` bytes)
into the sub-frame `stackAt (sp - 128#64) nextKeyInternalStackX` (`doReserveStack = 4208 ≤ 16560`),
the local scratch area (`memRegion (sp - 128#64) 8 ∗ memRegion (sp - 120#64) 36 ∗ memRegion (sp - 84#64) 4`),
and the 10 callee-saved 64-bit slots (`sp - 80 .. sp - 8`). -/
theorem stackAt_chainRecvKeyX_split (sp : BitVec 64) :
    stackAt sp chainRecvKeyStackX =
      stackAt (sp - 128#64) nextKeyInternalStackX ∗
      memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 120#64) 36 ∗
      memRegion (sp - 84#64) 4 ∗
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
        ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
        ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
        ((sp - 8#64) ↦₆₄ c9)) := by
  change memRegion (sp - BitVec.ofNat 64 16688) 16688 =
    memRegion (sp - 128#64 - BitVec.ofNat 64 16560) 16560 ∗ _
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16688) (n := 16560) (k := 128)
      (b' := sp - 128#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 120)
      (b' := sp - 120#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 120#64) (n := 36) (k := 84)
      (b' := sp - 84#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 84#64) (n := 4) (k := 80)
      (b' := sp - 80#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - BitVec.ofNat 64 16688) 16560 ∗
    (memRegion (sp - 128#64) 8 ∗
      (memRegion (sp - 120#64) 36 ∗
        (memRegion (sp - 84#64) 4 ∗ memRegion (sp - 80#64) (8 * 10)))) = _
  rw [ProofLib.memRegion_cells (sp - 80#64) 10 (by decide)]
  have hsub : sp - 128#64 - BitVec.ofNat 64 16560 = sp - BitVec.ofNat 64 16688 := by bv_kernel
  have hc10 : cells (sp - 80#64) 10 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
        ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
        ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
        ((sp - 8#64) ↦₆₄ c9)) := by
    cells_unfold
  rw [hsub, hc10]

/-- Rejoin the `recv_key` stack slots into `stackAt sp chainRecvKeyStackX`. -/
theorem rejoin_stack_chainRecvKeyX (sp : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    stackAt (sp - 128#64) nextKeyInternalStackX ∗
      memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 120#64) 36 ∗
      memRegion (sp - 84#64) 4 ∗
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
      ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
      ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
      ((sp - 8#64) ↦₆₄ c9) ⊢
      stackAt sp chainRecvKeyStackX := by
  rw [stackAt_chainRecvKeyX_split sp]
  have h10 :
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
      ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
      ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
      ((sp - 8#64) ↦₆₄ c9) ⊢
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
        ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
        ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
        ((sp - 8#64) ↦₆₄ c9)) :=
    Entails.sepExists_right c0 (Entails.sepExists_right c1 (Entails.sepExists_right c2
      (Entails.sepExists_right c3 (Entails.sepExists_right c4 (Entails.sepExists_right c5
        (Entails.sepExists_right c6 (Entails.sepExists_right c7 (Entails.sepExists_right c8
          (Entails.sepExists_right c9 (Entails.refl _))))))))))
  rw [show stackAt (sp - 128#64) nextKeyInternalStackX ∗
      memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 120#64) 36 ∗
      memRegion (sp - 84#64) 4 ∗
      ((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
      ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
      ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
      ((sp - 8#64) ↦₆₄ c9) =
      stackAt (sp - 128#64) nextKeyInternalStackX ∗
      memRegion (sp - 128#64) 8 ∗
      memRegion (sp - 120#64) 36 ∗
      memRegion (sp - 84#64) 4 ∗
      (((sp - 80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗
       ((sp - 56#64) ↦₆₄ c3) ∗ ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗
       ((sp - 32#64) ↦₆₄ c6) ∗ ((sp - 24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗
       ((sp - 8#64) ↦₆₄ c9)) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h10)))

/-- Split `memRegion (sp - 120#64) 36` into `(∃∗ l0 : BitVec 64, (sp - 120#64) ↦₆₄ l0) ∗ memRegion (sp - 112#64) 28`
for `str x11, [sp, #0x8]` at `0x60a0c`. -/
theorem memRegion_36_split_u64 (sp : BitVec 64) :
    memRegion (sp - 120#64) 36 =
      (∃∗ l0 : BitVec 64, (sp - 120#64) ↦₆₄ l0) ∗ memRegion (sp - 112#64) 28 := by
  rw [ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 28)
      (b' := sp - 112#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight (sp - 120#64)]

/-- Fold `((sp - 120#64) ↦₆₄ v) ∗ memRegion (sp - 112#64) 28` back into `memRegion (sp - 120#64) 36`. -/
theorem pointsTo64_memRegion_28_entails_36 (sp v : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v) ∗ memRegion (sp - 112#64) 28 ⊢ memRegion (sp - 120#64) 36 := by
  rw [memRegion_36_split_u64 sp]
  exact sepConj_mono_left (Entails.sepExists_right v (Entails.refl _))

/-- Split `memRegion (sp - 120#64) 36` into `(∃∗ d0 : BitVec 32, (sp - 120#64) ↦₃₂ d0) ∗ memRegion (sp - 116#64) 32`
for `str w8, [sp, #0x8]` at `0x60c5c`. -/
theorem memRegion_36_split_u32 (sp : BitVec 64) :
    memRegion (sp - 120#64) 36 =
      (∃∗ d0 : BitVec 32, (sp - 120#64) ↦₃₂ d0) ∗ memRegion (sp - 116#64) 32 := by
  rw [ProofLib.memRegion_split' (b := sp - 120#64) (n := 4) (k := 32)
      (b' := sp - 116#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_four (sp - 120#64)]

/-- Fold `((sp - 120#64) ↦₃₂ v) ∗ memRegion (sp - 116#64) 32` back into `memRegion (sp - 120#64) 36`. -/
theorem pointsTo32_memRegion_32_entails_36 (sp : BitVec 64) (v : BitVec 32) :
    ((sp - 120#64) ↦₃₂ v) ∗ memRegion (sp - 116#64) 32 ⊢ memRegion (sp - 120#64) 36 := by
  rw [memRegion_36_split_u32 sp]
  exact sepConj_mono_left (Entails.sepExists_right v (Entails.refl _))

/-- Fold `((sp - 120#64) ↦₃₂ fst) ∗ ((sp - 116#64) ↦₆₄ k0) ∗ ... ∗ ((sp - 92#64) ↦₆₄ k3)` into
`memRegion (sp - 120#64) 36`. -/
theorem pointsTo32_cells4_entails_memRegion_36_sp120 (sp : BitVec 64) (fst : BitVec 32)
    (k0 k1 k2 k3 : BitVec 64) :
    ((sp - 120#64) ↦₃₂ fst) ∗
      ((sp - 116#64) ↦₆₄ k0) ∗ ((sp - 108#64) ↦₆₄ k1) ∗
      ((sp - 100#64) ↦₆₄ k2) ∗ ((sp - 92#64) ↦₆₄ k3) ⊢
      memRegion (sp - 120#64) 36 := by
  rw [memRegion_36_split_u32 sp]
  have h4 : ((sp - 120#64) ↦₃₂ fst) ⊢ ∃∗ d0 : BitVec 32, (sp - 120#64) ↦₃₂ d0 :=
    Entails.sepExists_right fst (Entails.refl _)
  have h32 := cells4_entails_memRegion_32 (sp - 116#64) k0 k1 k2 k3
  simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at h32
  rw [show ((sp - 120#64) ↦₃₂ fst) ∗
      ((sp - 116#64) ↦₆₄ k0) ∗ ((sp - 108#64) ↦₆₄ k1) ∗
      ((sp - 100#64) ↦₆₄ k2) ∗ ((sp - 92#64) ↦₆₄ k3) =
    ((sp - 120#64) ↦₃₂ fst) ∗
      (((sp - 116#64) ↦₆₄ k0) ∗ ((sp - 108#64) ↦₆₄ k1) ∗
       ((sp - 100#64) ↦₆₄ k2) ∗ ((sp - 92#64) ↦₆₄ k3)) by ac_rfl]
  exact sepConj_mono h4 h32

/-- Split `stackAt (sp0 - 128#64) nextKeyInternalStackX` (`16560` B) into
`stackAt (sp0 - 128#64) doReserveStack` (`4208` B) and `memRegion (sp0 - 128#64 - 16560#64) 12352`. -/
theorem stackAt_nextKeyInternal_split_doReserve (sp : BitVec 64) :
    stackAt sp nextKeyInternalStackX =
      memRegion (sp - BitVec.ofNat 64 nextKeyInternalStackX) 12352 ∗
      stackAt sp doReserveStack := by
  change memRegion (sp - BitVec.ofNat 64 16560) 16560 =
    memRegion (sp - BitVec.ofNat 64 16560) 12352 ∗
    memRegion (sp - BitVec.ofNat 64 4208) 4208
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16560) (n := 12352) (k := 4208)
    (b' := sp - BitVec.ofNat 64 4208) rfl (by bv_omega) (by decide)

/-- Unpack `chainEpochAt A (gce, link) epPtr` to expose `link.recv` (`epPtr + 0x38` .. `epPtr + 0x70`)
for `<spqr::chain::Chain>::recv_key`. -/
theorem chainEpochAt_unpack_recv (A : RustAlloc) (gce : ChainEpochGhost)
    (epPtr : BitVec 64) (link : ChainEpoch) :
    chainEpochAt A (gce, link) epPtr ⊢
      ⌜link.recv.next.length ≤ gce.recv.next.cap.toNat ∧
        gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0 ∧
        link.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧
        gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
      chainEpochDirectionAt A epPtr gce.send link.send ∗
      ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
      ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
      ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 link.recv.next.length) ∗
      (gce.recv.next.ptr ↦ₛ link.recv.next) ∗
      vecU8Rest A gce.recv.next.cap gce.recv.next.ptr link.recv.next.length ∗
      ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
      ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
      ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 link.recv.prev.data.length) ∗
      (gce.recv.prev.ptr ↦ₛ link.recv.prev.data) ∗
      vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr link.recv.prev.data.length ∗
      ((epPtr + 0x68#64) ↦₃₂ link.recv.ctr) ∗
      memRegion (epPtr + 0x6c#64) 4 := by
  unfold chainEpochAt
  dsimp only
  unfold chainEpochDirectionAt keyHistoryAt
  have h1 := vecU8At_unpack A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr link.recv.next
  have h2 := vecU8At_unpack A ((epPtr + 0x38#64) + 0x18#64) gce.recv.prev.cap gce.recv.prev.ptr link.recv.prev.data
  have ha40 : epPtr + 0x38#64 + 8#64 = epPtr + 0x40#64 := by bv_kernel
  have ha48 : epPtr + 0x38#64 + 16#64 = epPtr + 0x48#64 := by bv_kernel
  have ha50 : epPtr + 0x38#64 + 0x18#64 = epPtr + 0x50#64 := by bv_kernel
  have ha58 : epPtr + 0x50#64 + 8#64 = epPtr + 0x58#64 := by bv_kernel
  have ha60 : epPtr + 0x50#64 + 16#64 = epPtr + 0x60#64 := by bv_kernel
  have ha68 : epPtr + 0x38#64 + 0x30#64 = epPtr + 0x68#64 := by bv_kernel
  have ha6c : epPtr + 0x38#64 + 0x34#64 = epPtr + 0x6c#64 := by bv_kernel
  rw [ha40, ha48] at h1
  rw [ha50, ha58, ha60] at h2
  rw [ha50, ha68, ha6c]
  refine Entails.trans (sepConj_mono_right (sepConj_mono h1 (sepConj_mono h2 (Entails.refl _)))) ?_
  rw [show ((vecU8At A epPtr gce.send.next.cap gce.send.next.ptr link.send.next ∗
        vecU8At A (epPtr + 0x18#64) gce.send.prev.cap gce.send.prev.ptr link.send.prev.data ∗
        ((epPtr + 0x30#64) ↦₃₂ link.send.ctr) ∗
        memRegion (epPtr + 0x34#64) 4) ∗
      ((⌜link.recv.next.length ≤ gce.recv.next.cap.toNat ∧
          gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0⌝ ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 link.recv.next.length) ∗
        (gce.recv.next.ptr ↦ₛ link.recv.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr link.recv.next.length) ∗
       ((⌜link.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧
           gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
         ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
         ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
         ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 link.recv.prev.data.length) ∗
         (gce.recv.prev.ptr ↦ₛ link.recv.prev.data) ∗
         vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr link.recv.prev.data.length) ∗
        ((epPtr + 0x68#64) ↦₃₂ link.recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4))) =
      ⌜link.recv.next.length ≤ gce.recv.next.cap.toNat ∧
        gce.recv.next.cap.toNat < 2 ^ 63 ∧ gce.recv.next.ptr ≠ 0⌝ ∗
      ⌜link.recv.prev.data.length ≤ gce.recv.prev.cap.toNat ∧
        gce.recv.prev.cap.toNat < 2 ^ 63 ∧ gce.recv.prev.ptr ≠ 0⌝ ∗
      ((vecU8At A epPtr gce.send.next.cap gce.send.next.ptr link.send.next ∗
        vecU8At A (epPtr + 0x18#64) gce.send.prev.cap gce.send.prev.ptr link.send.prev.data ∗
        ((epPtr + 0x30#64) ↦₃₂ link.send.ctr) ∗
        memRegion (epPtr + 0x34#64) 4) ∗
        ((epPtr + 0x38#64) ↦₆₄ gce.recv.next.cap) ∗
        ((epPtr + 0x40#64) ↦₆₄ gce.recv.next.ptr) ∗
        ((epPtr + 0x48#64) ↦₆₄ BitVec.ofNat 64 link.recv.next.length) ∗
        (gce.recv.next.ptr ↦ₛ link.recv.next) ∗
        vecU8Rest A gce.recv.next.cap gce.recv.next.ptr link.recv.next.length ∗
        ((epPtr + 0x50#64) ↦₆₄ gce.recv.prev.cap) ∗
        ((epPtr + 0x58#64) ↦₆₄ gce.recv.prev.ptr) ∗
        ((epPtr + 0x60#64) ↦₆₄ BitVec.ofNat 64 link.recv.prev.data.length) ∗
        (gce.recv.prev.ptr ↦ₛ link.recv.prev.data) ∗
        vecU8Rest A gce.recv.prev.cap gce.recv.prev.ptr link.recv.prev.data.length ∗
        ((epPtr + 0x68#64) ↦₃₂ link.recv.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4) by ac_rfl]
  refine Entails.pure_left fun ⟨hn1, hn2, hn3⟩ => ?_
  refine Entails.pure_left fun ⟨hp1, hp2, hp3⟩ => ?_
  exact Entails.pure_right ⟨hn1, hn2, hn3, hp1, hp2, hp3⟩ (Entails.refl _)

/-- Pack `chainEpochAt` when both `next` and `prev` are already folded as `vecU8At`. -/
theorem chainEpochAt_of_recv_vecs (A : RustAlloc) (gce : ChainEpochGhost) (prevGhost' : VecPin)
    (epPtr : BitVec 64) (link : ChainEpoch) (next' : Bytes) (prev' : KeyHistory) (ctr' : BitVec 32) :
    chainEpochDirectionAt A epPtr gce.send link.send ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next' ∗
      vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr prev'.data ∗
      ((epPtr + 0x68#64) ↦₃₂ ctr') ∗
      memRegion (epPtr + 0x6c#64) 4 ⊢
      chainEpochAt A
        ({ gce with recv := { gce.recv with prev := prevGhost' } },
         { link with recv := { ctr := ctr', next := next', prev := prev' } }) epPtr := by
  unfold chainEpochAt
  dsimp only
  unfold chainEpochDirectionAt keyHistoryAt
  have ha50 : epPtr + 0x38#64 + 0x18#64 = epPtr + 0x50#64 := by bv_kernel
  have ha68 : epPtr + 0x38#64 + 0x30#64 = epPtr + 0x68#64 := by bv_kernel
  have ha6c : epPtr + 0x38#64 + 0x34#64 = epPtr + 0x6c#64 := by bv_kernel
  rw [ha50, ha68, ha6c]
  rw [show (vecU8At A epPtr gce.send.next.cap gce.send.next.ptr link.send.next ∗
        vecU8At A (epPtr + 0x18#64) gce.send.prev.cap gce.send.prev.ptr link.send.prev.data ∗
        ((epPtr + 0x30#64) ↦₃₂ link.send.ctr) ∗
        memRegion (epPtr + 0x34#64) 4) ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next' ∗
      vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr prev'.data ∗
      ((epPtr + 0x68#64) ↦₃₂ ctr') ∗
      memRegion (epPtr + 0x6c#64) 4 =
      (vecU8At A epPtr gce.send.next.cap gce.send.next.ptr link.send.next ∗
        vecU8At A (epPtr + 0x18#64) gce.send.prev.cap gce.send.prev.ptr link.send.prev.data ∗
        ((epPtr + 0x30#64) ↦₃₂ link.send.ctr) ∗
        memRegion (epPtr + 0x34#64) 4) ∗
      (vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr next' ∗
       vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr prev'.data ∗
       ((epPtr + 0x68#64) ↦₃₂ ctr') ∗
       memRegion (epPtr + 0x6c#64) 4) by ac_rfl]
  exact Entails.refl _

private theorem list_zip_set {α β : Type} (xs : List α) (ys : List β) (i : Nat) (x : α) (y : β) :
    (xs.zip ys).set i (x, y) = (xs.set i x).zip (ys.set i y) := by
  induction xs generalizing ys i with
  | nil => simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      cases i with
      | zero => rfl
      | succ i => simp [ih]

/-- Combine `vecDequeRingBuf_set_physIdx` and `chainRepr_pack_sendKey`
after updating `link` at `epochIndex` with `recv'`. -/
theorem chainRepr_pack_recv (A : RustAlloc) (selfPtr : BitVec 64) (G : ChainGhost)
    (self : Chain) (epochIndex : Nat) (hi : epochIndex < self.links.length)
    (gce : ChainEpochGhost) (prevGhost' : VecPin)
    (recv' : ChainEpochDirection)
    (hhead : G.linksHead.toNat < G.linksCap.toNat)
    (hcap_lt : G.linksCap.toNat * 112 < 2 ^ 63)
    (hptr : G.linksPtr ≠ 0#64)
    (hlen_le : self.links.length ≤ G.linksCap.toNat)
    (hlen_eq : G.epochs.length = self.links.length) :
    let s := vecDequePhysIdx G.linksHead.toNat G.linksCap.toNat epochIndex
    let epPtr := G.linksPtr + BitVec.ofNat 64 (s * 112)
    (selfPtr ↦₆₄ G.linksCap) ∗ ((selfPtr + 8#64) ↦₆₄ G.linksPtr) ∗
      ((selfPtr + 16#64) ↦₆₄ G.linksHead) ∗
      ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
      A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
      chainEpochDirectionAt A epPtr gce.send (self.links[epochIndex]).send ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv'.next ∗
      vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr recv'.prev.data ∗
      ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
      memRegion (epPtr + 0x6c#64) 4 ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat
        G.linksPtr (G.epochs.zip self.links) s ∗
      ((selfPtr + 56#64) ↦₆₄ self.currentEpoch) ∗
      ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
      chainRestSendKeyAt A selfPtr G self ⊢
      chainRepr A selfPtr
        { self with links := self.links.set epochIndex { self.links[epochIndex] with recv := recv' } } := by
  intro s epPtr
  let gce' : ChainEpochGhost := { gce with recv := { gce.recv with prev := prevGhost' } }
  let link' : ChainEpoch := { self.links[epochIndex] with recv := recv' }
  have hep :
      chainEpochDirectionAt A epPtr gce.send (self.links[epochIndex]).send ∗
        vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv'.next ∗
        vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr recv'.prev.data ∗
        ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
        memRegion (epPtr + 0x6c#64) 4 ⊢
        chainEpochAt A (gce', link') epPtr :=
    chainEpochAt_of_recv_vecs A gce prevGhost' epPtr (self.links[epochIndex])
      recv'.next recv'.prev recv'.ctr
  have hzip_len : (G.epochs.zip self.links).length = self.links.length := by simp [hlen_eq]
  have hset := vecDequeRingBuf_set_physIdx A G.linksCap G.linksPtr G.linksHead
    (G.epochs.zip self.links) (gce', link') hhead hcap_lt hptr
    (by rw [hzip_len]; exact hlen_le) (by rw [hzip_len]; exact hi)
  rw [list_zip_set] at hset
  have hpack := chainRepr_pack_sendKey A selfPtr G self G.linksHead
    (G.epochs.set epochIndex gce') (self.links.set epochIndex link') self.sendEpoch
    (by simp [hlen_eq])
  simp only [List.length_set] at hpack
  refine Entails.trans ?_ hpack
  rw [show (selfPtr ↦₆₄ G.linksCap) ∗ ((selfPtr + 8#64) ↦₆₄ G.linksPtr) ∗
      ((selfPtr + 16#64) ↦₆₄ G.linksHead) ∗
      ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
      A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
      chainEpochDirectionAt A epPtr gce.send (self.links[epochIndex]).send ∗
      vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv'.next ∗
      vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr recv'.prev.data ∗
      ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
      memRegion (epPtr + 0x6c#64) 4 ∗
      vecDequeSlotsExcept (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat
        G.linksPtr (G.epochs.zip self.links) s ∗
      ((selfPtr + 56#64) ↦₆₄ self.currentEpoch) ∗
      ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
      chainRestSendKeyAt A selfPtr G self =
      (selfPtr ↦₆₄ G.linksCap) ∗ ((selfPtr + 8#64) ↦₆₄ G.linksPtr) ∗
      ((selfPtr + 16#64) ↦₆₄ G.linksHead) ∗
      ((selfPtr + 24#64) ↦₆₄ BitVec.ofNat 64 self.links.length) ∗
      ((A.live G.linksPtr (G.linksCap.toNat * 112) 8 ∗
        (chainEpochDirectionAt A epPtr gce.send (self.links[epochIndex]).send ∗
          vecU8At A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr recv'.next ∗
          vecU8At A (epPtr + 0x50#64) prevGhost'.cap prevGhost'.ptr recv'.prev.data ∗
          ((epPtr + 0x68#64) ↦₃₂ recv'.ctr) ∗
          memRegion (epPtr + 0x6c#64) 4) ∗
        vecDequeSlotsExcept (chainEpochAt A) 112 G.linksCap.toNat G.linksHead.toNat
          G.linksPtr (G.epochs.zip self.links) s) ∗
       ((selfPtr + 56#64) ↦₆₄ self.currentEpoch) ∗
       ((selfPtr + 64#64) ↦₆₄ self.sendEpoch) ∗
       chainRestSendKeyAt A selfPtr G self) by ac_rfl]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (Entails.trans (sepConj_mono_right (sepConj_mono_left hep)) hset)))))

/-! ## Epilogue (`+248`), `Ok` Return (`+708`), and `Err` Return Tails -/

/-- Normal-return postcondition of `SepWPp` for `<spqr::chain::Chain>::recv_key`. -/
abbrev recvKeyPost (hkdf : HkdfFn) (A : RustAlloc) (x : ChainRecvKeyGhost) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P' ⊢ (chainRecvKeySpecX hkdf A).post x s0 sf)

/-- Panic-outcome postcondition of `SepWPp` for `<spqr::chain::Chain>::recv_key`. -/
abbrev recvKeyPanic (hkdf : HkdfFn) (A : RustAlloc) (x : ChainRecvKeyGhost) (s0 : State)
    (R : SepProp) : State → SepProp → Prop :=
  fun sf P' => (sf.mem ⊨ P' ∗ R) → (sf.mem ⊨ (chainRecvKeySpecX hkdf A).onPanic x s0 sf ∗ R)

/-- Untouched portions of the 128-byte `recv_key` stack frame (`[sp, #0x0..#0x8)`,
`[sp, #0x2c..#0x30)`, and saved registers `[sp, #0x30..#0x80)`). -/
def recvKeyFrameRestAt (s0 : State) (c3 : BitVec 64) : SepProp :=
  memRegion (s0.sp - 128#64) 8 ∗
    memRegion (s0.sp - 84#64) 4 ∗
    calleeSavedRecvKeyAt s0.sp s0 c3

/-- State invariant across the body of `<spqr::chain::Chain>::recv_key` after frame allocation
(`sp = s0.sp - 128#64`). -/
structure RecvKeyStateInv (img : Obj.Image) (s0 s : State) : Prop where
  hF : ImgCallInv img s
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 128#64
  hsp0_align : s0.spAligned = true
  hx26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  hx27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  hx28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  htrace : s.trace = s0.trace
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem RecvKeyStateInv.spAligned {img : Obj.Image} {s0 s : State}
    (h : RecvKeyStateInv img s0 s) : s.spAligned = true := by
  have h0 := h.hsp0_align
  have hsp := h.hsp
  simp only [State.spAligned, hsp] at h0 ⊢
  revert h0; bv_kernel

theorem allowPanic_recvKey_oom {hkdf : HkdfFn} {A : RustAlloc}
    {x : ChainRecvKeyGhost} {s0 sf : State} {P R : SepProp}
    (hoom : allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (chainRecvKeySpecX hkdf A).onPanic x s0 sf ∗ R := by
  dsimp only [chainRecvKeySpecX]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨Or.inr hoom, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

theorem allowPanic_recvKey_panic {hkdf : HkdfFn} {A : RustAlloc}
    {x : ChainRecvKeyGhost} {s0 sf : State} {P R : SepProp}
    (hpan : (Chain.recvKey hkdf x.self x.epoch x.index).isPanic = true)
    (htr : sf.trace = s0.trace) (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ (chainRecvKeySpecX hkdf A).onPanic x s0 sf ∗ R := by
  dsimp only [chainRecvKeySpecX]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨Or.inl ⟨hpan, htr⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap P)) hm⟩

theorem SepWPp.mono_pre {prog : Program} {target_pc : BitVec 64} {s : State}
    (P' : SepProp) {P : SepProp} {post panic : State → SepProp → Prop}
    (h : P ⊢ P') (hwp : SepWPp prog target_pc s P' post panic) :
    SepWPp prog target_pc s P post panic :=
  fun R' hm hL => hwp R' (Satisfies.mono (sepConj_mono_left h) hm) hL

/-- Epilogue of `recv_key` at `+248` (`0x609c8 .. 0x609e0`): restores `x19..x25, x29, x30`,
deallocates the 128-byte frame (`add sp, sp, #0x80`), and returns to `s0.readReg64 .x30`. -/
theorem recvKey_epilogue {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 248#64) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  unfold recvKeyFrameRestAt calleeSavedRecvKeyAt
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx26
  wp_norm_hyp hx27
  wp_norm_hyp hx28
  wp_norm_hyp htrace
  wp_norm_hyp hvregs
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (rejoin_stack_chainRecvKeyX s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) c3
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
  dsimp only [chainRecvKeySpecX]
  refine Entails.pure_right (by wp_norm_goal) ?_
  sep_frame

/-- `Ok(outKey)` return tail at `+708` (`0x60b94` -> `+56` -> `+248`):
stores `(0#64, 32#64, p_key, 32#64)` into `x.out` (`x19`) and jumps to the epilogue. -/
theorem recvKey_ok_from_708 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (self' : Chain) (outKey : Bytes) (p_key : BitVec 64)
    (hp_key : p_key ≠ 0#64) (hlen_key : outKey.length = 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 708#64)
    (hx0 : s.readReg64 (.gpr 0#5) = p_key)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        A.live p_key 32 1 ∗ (p_key ↦ₛ outKey) ∗
        chainRepr A x.selfPtr self' ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  have h_epi := @recvKey_epilogue img hkdf A ext x s0 c3 R
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_ok_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v16
  apply SepWPp.exists_elim; intro v24
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx0
  wp_norm_hyp hx19
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hF ?_
  wp_steps
  refine SepWP.fold (recvKeyOkAt_alloc_intro A x.out p_key outKey hp_key hlen_key) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by rw [← hvregs]; wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

/-- `Err(Error::KeyTrimmed(index))` return tail at `+884` (`0x60c44` -> `+236` -> `+248`)
when `(w8 : BitVec 8) = 10#8`. -/
theorem recvKey_err_keyTrimmed_from_884 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 884#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 8 = 10#8)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  have h_epi := @recvKey_epilogue img hkdf A ext x s0 c3 R
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_u32_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hw8
  wp_norm_hyp hx19
  wp_norm_hyp hw20
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hF ?_
  wp_steps
  refine SepWP.fold (recvKeyErrAt_keyTrimmed_intro x.out x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by rw [← hvregs]; wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

/-- `Err(Error::KeyAlreadyRequested(index))` return tail at `+880` (`0x60c40` -> `+884` -> `+236` -> `+248`). -/
theorem recvKey_err_keyAlreadyRequested_from_880 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 880#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  have h_epi := @recvKey_epilogue img hkdf A ext x s0 c3 R
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_u32_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx19
  wp_norm_hyp hw20
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hF ?_
  wp_steps
  refine SepWP.fold (recvKeyErrAt_keyAlreadyRequested_intro x.out x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by rw [← hvregs]; wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

/-- `Err(Error::KeyJump(ctr, index))` return tail at `+204` (`0x6099c` -> `+248`). -/
theorem recvKey_err_keyJump_from_204 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (ctr : BitVec 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyJump ctr x.index)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 204#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  have h_epi := @recvKey_epilogue img hkdf A ext x s0 c3 R
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_jump_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v12
  apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hw8
  wp_norm_hyp hx19
  wp_norm_hyp hw20
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hF ?_
  wp_steps
  refine SepWP.fold (recvKeyErrAt_keyJump_intro x.out ctr x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by rw [← hvregs]; wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

/-- `Err(Error::EpochOutOfRange(epoch))` return tail at `+228` (`0x609b4` -> `+248`). -/
theorem recvKey_err_epochOutOfRange_from_228 {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 228#64)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x5b4d8 1248
  clear hfn
  have h_epi := @recvKey_epilogue img hkdf A ext x s0 c3 R
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_epoch_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0
  apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun
  wp_norm_hyp hsp_align
  wp_norm_hyp hsp
  wp_norm_hyp hx2
  wp_norm_hyp hx19
  refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hF ?_
  wp_steps
  refine SepWP.fold (recvKeyErrAt_epochOutOfRange_intro x.out x.epoch) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF'
  have hinv' : RecvKeyStateInv img s0 _ :=
    ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
     by rw [← hx26]; wp_norm_goal,
     by rw [← hx27]; wp_norm_goal,
     by rw [← hx28]; wp_norm_goal,
     htrace,
     by rw [← hvregs]; wp_norm_goal⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

/-! ## Relocatable `[LibsignalPlacement]` Tail Helpers (`blkPC_366`) -/

structure RecvKeyPlacedStateInv (lsmpl : Obj.MultiPlacement) (s0 s : State) : Prop where
  hF : LsCallInv lsmpl s.mem
  hrun : s.status = .Running
  hsp : s.sp = s0.sp - 128#64
  hsp0_align : s0.spAligned = true
  hx26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  hx27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  hx28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  htrace : s.trace = s0.trace
  hvregs : calleeSavedVRegs s = calleeSavedVRegs s0

theorem RecvKeyPlacedStateInv.spAligned {lsmpl : Obj.MultiPlacement} {s0 s : State}
    (h : RecvKeyPlacedStateInv lsmpl s0 s) : s.spAligned = true := by
  have h0 := h.hsp0_align; have hsp := h.hsp
  simp only [State.spAligned, hsp] at h0 ⊢; revert h0; bv_kernel

theorem recvKey_epilogue_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 248#64) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        recvKeyPostAt A x.selfPtr x.out x.self (Chain.recvKey hkdf x.self x.epoch x.index) ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  unfold recvKeyFrameRestAt calleeSavedRecvKeyAt
  wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28
  wp_norm_hyp htrace; wp_norm_hyp hvregs; apply SepWPp.of_sepWP_ret; wp_steps
  refine SepWP.fold (rejoin_stack_chainRecvKeyX s0.sp
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x25) c3
    (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22) (s0.readReg64 .x21)
    (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ⟨by wp_norm_goal, by unfold CalleeSavedPreserved; wp_norm_goal, ?_⟩
  dsimp only [chainRecvKeySpecX]; refine Entails.pure_right (by wp_norm_goal) ?_; sep_frame

theorem recvKey_ok_from_708_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (self' : Chain) (outKey : Bytes) (p_key : BitVec 64)
    (hp_key : p_key ≠ 0#64) (hlen_key : outKey.length = 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .ok (self', outKey))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 708#64)
    (hx0 : s.readReg64 (.gpr 0#5) = p_key)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ A.live p_key 32 1 ∗ (p_key ↦ₛ outKey) ∗ chainRepr A x.selfPtr self' ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_ok_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v16; apply SepWPp.exists_elim; intro v24
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx0; wp_norm_hyp hx19
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hF ?_
  wp_steps; refine SepWP.fold (recvKeyOkAt_alloc_intro A x.out p_key outKey hp_key hlen_key) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by rw [← hvregs]; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

theorem recvKey_err_keyTrimmed_from_884_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyTrimmed x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 884#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 8 = 10#8)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_u32_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hF ?_
  wp_steps; refine SepWP.fold (recvKeyErrAt_keyTrimmed_intro x.out x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by rw [← hvregs]; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

theorem recvKey_err_keyAlreadyRequested_from_880_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyAlreadyRequested x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 880#64)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_u32_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v12
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hF ?_
  wp_steps; refine SepWP.fold (recvKeyErrAt_keyAlreadyRequested_intro x.out x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by rw [← hvregs]; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

theorem recvKey_err_keyJump_from_204_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (ctr : BitVec 32)
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.keyJump ctr x.index)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 204#64)
    (hw8 : (s.readReg64 (.gpr 8#5)).setWidth 32 = ctr)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_jump_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8
  apply SepWPp.exists_elim; intro v12; apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hw8; wp_norm_hyp hx19; wp_norm_hyp hw20
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hF ?_
  wp_steps; refine SepWP.fold (recvKeyErrAt_keyJump_intro x.out ctr x.index) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by rw [← hvregs]; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

theorem recvKey_err_epochOutOfRange_from_228_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hres : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 228#64)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗ chainRepr A x.selfPtr x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗ memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗ A.pool)
      (recvKeyPost hkdf A x s0) (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x s0 c3 R
  dsimp only [prog] at *
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  rw [memRegion_32_err_epoch_split x.out]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro v0; apply SepWPp.exists_elim; intro v8; apply SepWPp.exists_elim; intro v16
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp; wp_norm_hyp hx2; wp_norm_hyp hx19
  refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hF ?_
  wp_steps; refine SepWP.fold (recvKeyErrAt_epochOutOfRange_intro x.out x.epoch) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal); intro hF'
  have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
    ⟨hF', (by wp_norm_goal), (by wp_norm_goal), hsp0_align, (by rw [← hx26]; wp_norm_goal),
     (by rw [← hx27]; wp_norm_goal), (by rw [← hx28]; wp_norm_goal), htrace, (by rw [← hvregs]; wp_norm_goal)⟩
  refine SepWPp.mono_pre _ ?_ (h_epi _ hinv' (by wp_norm_goal))
  rw [hres]; dsimp only [recvKeyPostAt]; sep_frame

end CryptoVerification.SpqrV1.ChainProofs
