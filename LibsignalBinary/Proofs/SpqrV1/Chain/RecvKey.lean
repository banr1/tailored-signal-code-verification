/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyGet
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAdvance
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyPop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `<spqr::chain::Chain>::recv_key`

Proves fixed-image (`chainRecvKey_ok_of_contracts_x`, `chainRecvKey_ok_ext_x`,
`chainRecvKey_ok_of_contracts_ext`) and relocatable `[LibsignalPlacement]` contracts for
`<spqr::chain::Chain>::recv_key` (`0x608d0`, Block `366`, 312 instructions).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Alloc
open ChainAddEpochFacts ChainNewFacts NextKeyInternalFacts ChainSendKeyFacts
open CryptoVerification.CodeLayout
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre

local macro "sep_elim_10 "
    c0:ident c1:ident c2:ident c3:ident c4:ident
    c5:ident c6:ident c7:ident c8:ident c9:ident : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro $c0:ident; apply SepWPp.exists_elim; intro $c1:ident
    apply SepWPp.exists_elim; intro $c2:ident; apply SepWPp.exists_elim; intro $c3:ident
    apply SepWPp.exists_elim; intro $c4:ident; apply SepWPp.exists_elim; intro $c5:ident
    apply SepWPp.exists_elim; intro $c6:ident; apply SepWPp.exists_elim; intro $c7:ident
    apply SepWPp.exists_elim; intro $c8:ident; apply SepWPp.exists_elim; intro $c9:ident))

/-! ## Comparison and Parameter Lemmas for `recv_key` Entry (`+64..+200`) -/

theorem lt64_props {a b : BitVec 64} (h : a < b) :
    BitVec.ult a b = true ∧ BitVec.ule b a = false := by
  have hlt : a.toNat < b.toNat := BitVec.lt_def.mp h
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule] <;> omega

theorem ge64_props {a b : BitVec 64} (h : ¬ a < b) :
    BitVec.ult a b = false ∧ BitVec.ule b a = true := by
  have hge : b.toNat ≤ a.toNat := by
    by_contra hlt; exact h (BitVec.lt_def.mpr (by omega))
  refine ⟨?_, ?_⟩ <;> simp [BitVec.ult, BitVec.ule] <;> omega

theorem back_ge64_props {d : BitVec 64} {len : Nat}
    (hge : d.toNat ≥ len) (hlen : len < 2 ^ 63) :
    BitVec.ult d (BitVec.ofNat 64 len) = false ∧
    BitVec.ule (BitVec.ofNat 64 len) d = true := by
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;>
    omega

theorem back_lt64_props {d : BitVec 64} {len : Nat}
    (hlt : d.toNat < len) (hlen : len < 2 ^ 63) :
    BitVec.ult d (BitVec.ofNat 64 len) = true ∧
    BitVec.ule (BitVec.ofNat 64 len) d = false := by
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64] <;>
    omega

theorem back_add_not_no_borrow {d : BitVec 64} {len : Nat}
    (hlt : d.toNat < len) (hlen : len < 2 ^ 63) :
    BitVec.ult (BitVec.ofNat 64 len + ~~~d) (BitVec.ofNat 64 len) = true ∧
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 len + ~~~d) = false := by
  have hlen64 : len < 18446744073709551616 := by omega
  rw [add_not_eq_ofNat_sub hlt]
  have hsub64 : len - 1 - d.toNat < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [BitVec.ult, BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64] <;>
    omega

private theorem ofNat_lt_props {i len : Nat} (hi : i < len) (hlen : len < 2 ^ 63) :
    BitVec.ule (BitVec.ofNat 64 len) (BitVec.ofNat 64 i) = false ∧
    BitVec.ult (BitVec.ofNat 64 i) (BitVec.ofNat 64 len) = true := by
  have hi64 : i < 18446744073709551616 := by omega
  have hlen64 : len < 18446744073709551616 := by omega
  refine ⟨?_, ?_⟩ <;>
    simp [BitVec.ule, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt hlen64] <;>
    omega

theorem cmp32_eq_props {a b : BitVec 32} (h : a = b) :
    BitVec.ult a b = false ∧ BitVec.ult b a = false ∧
    BitVec.ule a b = true ∧ BitVec.ule b a = true ∧
    (a == b) = true ∧ (a - b == 0#32) = true := by
  subst h
  refine ⟨?_, ?_, ?_, ?_, beq_self_eq_true a, by simp⟩ <;>
    simp [BitVec.ult, BitVec.ule]

theorem cmp32_lt_props {a b : BitVec 32} (h : a < b) :
    BitVec.ult a b = true ∧ BitVec.ult b a = false ∧
    BitVec.ule a b = true ∧ BitVec.ule b a = false ∧
    (a == b) = false ∧ (a - b == 0#32) = false := by
  have hlt : a.toNat < b.toNat := BitVec.lt_def.mp h
  have hne : a ≠ b := fun heq => by subst heq; omega
  refine ⟨?_, ?_, ?_, ?_, beq_false_of_ne hne, ?_⟩
  · simp [BitVec.ult]; omega
  · simp [BitVec.ult]; omega
  · simp [BitVec.ule]; omega
  · simp [BitVec.ule]; omega
  · rw [beq_eq_false_iff_ne]; intro heq; apply hne; revert heq; bv_kernel

theorem cmp32_gt_props {a b : BitVec 32} (h : b < a) :
    BitVec.ult a b = false ∧ BitVec.ult b a = true ∧
    BitVec.ule a b = false ∧ BitVec.ule b a = true ∧
    (a == b) = false ∧ (a - b == 0#32) = false := by
  have ⟨h1, h2, h3, h4, _, _⟩ := cmp32_lt_props h
  have hne : a ≠ b := fun heq => BitVec.lt_irrefl a (heq ▸ h)
  refine ⟨h2, h1, h4, h3, beq_false_of_ne hne, ?_⟩
  rw [beq_eq_false_iff_ne]; intro heq; apply hne; revert heq; bv_kernel

theorem maxJumpOrDefault_csel_eq (p : ChainParamsPB) :
    (if (p.maxJump == 0#32) = true then 0x61a8#32 else p.maxJump) = p.maxJumpOrDefault ∧
    (if (p.maxJump - 0#32 == 0#32) = true then 0x61a8#32 else p.maxJump) = p.maxJumpOrDefault := by
  unfold ChainParamsPB.maxJumpOrDefault DEFAULT_CHAIN_PARAMS
  simp only [BitVec.sub_zero, Bool.and_self]
  by_cases h0 : p.maxJump = 0#32
  · rw [h0]; decide
  · have hpos : p.maxJump > 0#32 :=
      BitVec.lt_def.mpr (Nat.pos_of_ne_zero fun h => h0 (BitVec.eq_of_toNat_eq h))
    simp [h0, hpos]

theorem zeroExtend64_truncate32_beq_zero (v : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) == 0#64) = (v.setWidth 32 == 0#32) := by
  change (BitVec.zeroExtend 64 (v.setWidth 32) == 0#64) = (v.setWidth 32 == 0#32)
  by_cases h : v.setWidth 32 = 0#32
  · rw [h]; rfl
  · have hne : BitVec.zeroExtend 64 (v.setWidth 32) ≠ 0#64 := by
      intro hz; apply h; revert hz; bv_kernel
    rw [beq_false_of_ne hne, beq_false_of_ne h]

theorem jump_cmp_props (atIdx ctr : BitVec 32) (p : ChainParamsPB) :
    BitVec.ult p.maxJumpOrDefault (atIdx - ctr) = decide (atIdx - ctr > p.maxJumpOrDefault) ∧
    BitVec.ule (atIdx - ctr) p.maxJumpOrDefault = !decide (atIdx - ctr > p.maxJumpOrDefault) := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.ult_eq_decide]; rfl
  · rw [BitVec.ule_eq_decide]
    by_cases h : atIdx - ctr > p.maxJumpOrDefault
    · have hlt := BitVec.lt_def.mp h
      rw [decide_eq_true h, decide_eq_false (by omega)]; rfl
    · have hle : ¬ (p.maxJumpOrDefault.toNat < (atIdx - ctr).toNat) :=
        fun hlt => h (BitVec.lt_def.mpr hlt)
      rw [decide_eq_false h, decide_eq_true (by omega)]; rfl

theorem chainRestSendKeyAt_params_eq (A : RustAlloc) (selfPtr : BitVec 64)
    (G : ChainGhost) (self : Chain) :
    chainRestSendKeyAt A selfPtr G self =
      vecU8At A (selfPtr + 32#64) G.nextRoot.cap G.nextRoot.ptr self.nextRoot ∗
      ((selfPtr + 72#64) ↦₃₂ self.params.maxJump) ∗
      ((selfPtr + 76#64) ↦₃₂ self.params.maxOooKeys) ∗
      directionAt (selfPtr + 80#64) self.dir ∗
      memRegion (selfPtr + 84#64) 4 := by
  unfold chainRestSendKeyAt chainParamsAt
  have h76 : selfPtr + 72#64 + 4#64 = selfPtr + 76#64 := by bv_kernel
  rw [h76]
  ac_rfl

theorem recvKeyFrameRestAt_def (s0 : State) (c3 : BitVec 64) :
    recvKeyFrameRestAt s0 c3 =
      memRegion (s0.sp - 128#64) 8 ∗
      memRegion (s0.sp - 84#64) 4 ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 56#64) ↦₆₄ c3) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) := by
  unfold recvKeyFrameRestAt calleeSavedRecvKeyAt
  ac_rfl

/-! ## Non-Zero Entry Path `recvKey_from_64` (`0x60910`) -/

set_option maxHeartbeats 1200000 in
/-- Continuation of `<spqr::chain::Chain>::recv_key` at `+64` (`0x60910`) when
`¬ (x.epoch = 0#64 ∧ x.index = 0#32)`:
computes `self.epochIdx(epoch)` (`+228` on `EpochOutOfRange`), indexes `self.links[epochIndex].recv`,
and dispatches on `Ord::cmp(&index, &recv.ctr)` to:
* `+880` (`recvKey_err_keyAlreadyRequested_from_880`) when `index = recv.ctr`,
* `+276` (`recvKey_get_from_276`) when `index < recv.ctr`,
* `+204` (`recvKey_err_keyJump_from_204`) when `index > recv.ctr` and `index - recv.ctr > maxJump`,
* `+360` (`recvKey_advance_from_360`) when `index > recv.ctr` and `index - recv.ctr ≤ maxJump`. -/
theorem recvKey_from_64 {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img))
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hfits : RecvPrevFits x.self)
    (hne_zero : ¬ (x.epoch = 0#64 ∧ x.index = 0#32))
    (s : State) (hinv : RecvKeyStateInv img s0 s)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName + 64#64)
    (hx1 : s.readReg64 (.gpr 1#5) = x.selfPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := libsignalSessionCode.rebase img.base (Rust.withPanics ext)
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainAt A x.selfPtr x.G x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX)) extra)
      (recvKeyPostCore extra hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  have h_err228 := fun {R0 : SepProp} => @recvKey_err_epochOutOfRange_from_228 img hkdf A ext x s0 c3 R0
  have h_err880 := fun {R0 : SepProp} => @recvKey_err_keyAlreadyRequested_from_880 img hkdf A ext x s0 c3 R0
  have h_err204 := fun {R0 : SepProp} => @recvKey_err_keyJump_from_204 img hkdf A ext x s0 c3 R0
  have h_get276 := fun {R0 : SepProp} => @recvKey_get_from_276 img hkdf A ext hshim halloc x s0 c3 R0
  have h_adv360 := @recvKey_advance_from_360 extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc hdoRes x s0 c3 R
  clear hsub_extra hnextKey hnextKeyPanic hshim halloc hdoRes hfn
  dsimp only [prog] at *
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.fold (chainAt_unpack_sendKey A x.selfPtr x.G x.self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx2; wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp htrace
  by_cases hgt_curr : x.epoch > x.self.currentEpoch
  ·
    have ⟨hult_curr, hule_curr⟩ := lt64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 228#64) hF ?_
    wp_steps
    refine SepWP.fold (chainRepr_pack_sendKey A x.selfPtr x.G x.self
      x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
      recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero (epochIdx_of_gt x.self x.epoch hgt_curr)
    refine recvKey_frame_extra ?_
      (fun {R0} => h_err228 (R0 := R0) hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have ⟨hult_curr, hule_curr⟩ := ge64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    by_cases hback_ge : (x.self.currentEpoch - x.epoch).toNat ≥ x.self.links.length
    ·
      have ⟨hult_back, hule_back⟩ := back_ge64_props hback_ge (by omega : x.self.links.length < 2 ^ 63)
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 228#64) hF ?_
      wp_steps
      refine SepWP.fold (chainRepr_pack_sendKey A x.selfPtr x.G x.self
        x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
      have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
        recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero
          (epochIdx_of_back_ge x.self x.epoch hgt_curr hback_ge)
      refine recvKey_frame_extra ?_
        (fun {R0} => h_err228 (R0 := R0) hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
    ·
      have hback_lt : (x.self.currentEpoch - x.epoch).toNat < x.self.links.length := by omega
      have hlen_lt63 : x.self.links.length < 2 ^ 63 := by omega
      have ⟨hult_back, hule_back⟩ := back_lt64_props hback_lt hlen_lt63
      have ⟨hult_nb, hule_nb⟩ := back_add_not_no_borrow hback_lt hlen_lt63
      let epochIndex := x.self.links.length - 1 - (x.self.currentEpoch - x.epoch).toNat
      have hi_ep : epochIndex < x.self.links.length := by dsimp [epochIndex]; omega
      have hidx_eq : x.self.epochIdx x.epoch = .ok epochIndex :=
        epochIdx_of_lt x.self x.epoch hgt_curr hback_lt
      have hadd_not :
          BitVec.ofNat 64 x.self.links.length + ~~~(x.self.currentEpoch - x.epoch) =
            BitVec.ofNat 64 epochIndex :=
        add_not_eq_ofNat_sub hback_lt
      have hzip_le : (x.G.epochs.zip x.self.links).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
      have hzip_i : epochIndex < (x.G.epochs.zip x.self.links).length := by simp [hlen_eq, hi_ep]
      refine SepWPp.fold
        (vecDequeRingBuf_get_physIdx A x.G.linksCap x.G.linksPtr x.G.linksHead
          (x.G.epochs.zip x.self.links) hzip_le hzip_i) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hhead, _, _⟩
      have hzip_geti : (x.G.epochs.zip x.self.links)[epochIndex] =
          (x.G.epochs[epochIndex]'(by omega), x.self.links[epochIndex]'hi_ep) := by
        simp [List.getElem_zip]
      rw [hzip_geti]
      let gce := x.G.epochs[epochIndex]'(by omega)
      let link := x.self.links[epochIndex]'hi_ep
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      refine SepWPp.fold (chainEpochAt_unpack_recv A gce epPtr link) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hn_le, hn_cap, hn_ptr, hp_le, hp_cap, hp_ptr⟩
      refine SepWPp.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self)) (by sep_focus) ?_
      have hmadd := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi_ep hlen_le) hcap_lt
      have hres_ep : Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (recv', out) ← link.recv.key hkdf x.index x.self.params
          let links' := x.self.links.set epochIndex { link with recv := recv' }
          return ({ x.self with links := links' }, out)) :=
        recvKey_of_epochIdx_ok hkdf x.self x.epoch x.index epochIndex link hne_zero hidx_eq
          (List.getElem?_eq_getElem hi_ep)
      have hult_ei : (BitVec.ofNat 64 epochIndex).ult (BitVec.ofNat 64 x.self.links.length) = true :=
        hadd_not ▸ hult_nb
      have hule_ei : (BitVec.ofNat 64 x.self.links.length).ule (BitVec.ofNat 64 epochIndex) = false :=
        hadd_not ▸ hule_nb
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      wp_norm_hyp hult_nb; wp_norm_hyp hule_nb
      wp_norm_hyp hadd_not; wp_norm_hyp hult_ei; wp_norm_hyp hule_ei; wp_norm_hyp hmadd
      by_cases heq_ctr : x.index = link.recv.ctr
      ·
        have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_eq_props heq_ctr
        wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
        wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
        refine SepWPp.of_sepWP_inImage (mid := entry_addr + 880#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
          link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
          link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
        have hpack := chainRepr_pack_recv A x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
          hhead hcap_lt hptr hlen_le hlen_eq
        dsimp only [s_idx, epPtr, link] at hpack ⊢
        have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
            x.self.links := List.set_getElem_self hi_ep
        rw [hset_self] at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyStateInv img s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hres_already : Chain.recvKey hkdf x.self x.epoch x.index =
            .error (.err (.keyAlreadyRequested x.index)) := by
          rw [hres_ep, ced_key_of_eq hkdf link.recv x.index x.self.params heq_ctr]
          rfl
        refine recvKey_frame_extra ?_
          (fun {R0} => h_err880 (R0 := R0) hres_already _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · by_cases hlt_ctr : x.index < link.recv.ctr
        ·
          have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_lt_props hlt_ctr
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          refine SepWPp.of_sepWP_inImage (mid := entry_addr + 276#64) hF ?_
          wp_steps
          refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
            link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
            link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF'
          have hinv' : RecvKeyStateInv img s0 _ :=
            ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
             by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
          have hres_get : Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
            rw [hres_ep, ced_key_of_lt hkdf link.recv x.index x.self.params hlt_ctr]
            dsimp only [link]
            cases (x.self.links[epochIndex]'hi_ep).recv.prev.get x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params <;> rfl
          refine recvKey_frame_extra ?_
            (fun {R0} => h_get276 (R0 := R0) epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hres_get
              _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
          unfold chainOuterRecvAt
          dsimp only [s_idx, epPtr, link, gce]
          sep_frame
        ·
          have hgt_ctr : link.recv.ctr < x.index := by
            apply BitVec.lt_def.mpr
            have h1 : ¬ (x.index.toNat < link.recv.ctr.toNat) := fun h => hlt_ctr (BitVec.lt_def.mpr h)
            have h2 : x.index.toNat ≠ link.recv.ctr.toNat := fun h => heq_ctr (BitVec.eq_of_toNat_eq h)
            omega
          have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_gt_props hgt_ctr
          have ⟨hmaxJ1, hmaxJ2⟩ := maxJumpOrDefault_csel_eq x.self.params
          have ⟨hult_jmp, hule_jmp⟩ := jump_cmp_props x.index link.recv.ctr x.self.params
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          wp_norm_hyp hmaxJ1; wp_norm_hyp hmaxJ2
          wp_norm_hyp hult_jmp; wp_norm_hyp hule_jmp
          by_cases hjump : x.index - link.recv.ctr > x.self.params.maxJumpOrDefault
          ·
            have hjump_t : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = true :=
              decide_eq_true hjump
            wp_norm_hyp hjump_t
            refine SepWPp.of_sepWP_inImage (mid := entry_addr + 204#64) hF ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
              link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
              link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
            have hpack := chainRepr_pack_recv A x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
              hhead hcap_lt hptr hlen_le hlen_eq
            dsimp only [s_idx, epPtr, link] at hpack ⊢
            have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
                x.self.links := List.set_getElem_self hi_ep
            rw [hset_self] at hpack
            refine SepWP.fold hpack (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyStateInv img s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
            have hres_jmp : Chain.recvKey hkdf x.self x.epoch x.index =
                .error (.err (.keyJump link.recv.ctr x.index)) := by
              rw [hres_ep, ced_key_of_gt_jump hkdf link.recv x.index x.self.params hgt_ctr hjump]
              rfl
            refine recvKey_frame_extra ?_
              (fun {R0} => h_err204 (R0 := R0) link.recv.ctr hres_jmp _ hinv' (by wp_norm_goal)
                (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            sep_frame
          ·
            have hjump_f : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = false :=
              decide_eq_false hjump
            wp_norm_hyp hjump_f
            refine SepWPp.of_sepWP_inImage (mid := entry_addr + 360#64) hF ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyStateInv img s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
            have hp_fit0 : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 61 :=
              hfits _ (List.getElem_mem hi_ep)
            refine SepWPp.mono_pre _ ?_
              (h_adv360 epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
                hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hp_fit0 hgt_ctr hjump hres_ep
                _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
                (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            unfold chainOuterRecvAt
            dsimp only [s_idx, epPtr, link, gce]
            sep_frame

/-! ## Fixed-Image Entry Contracts -/

theorem chainAt_entails_chainRepr (A : RustAlloc) (selfPtr : BitVec 64)
    (G : ChainGhost) (self : Chain) :
    chainAt A selfPtr G self ⊢ chainRepr A selfPtr self :=
  Entails.sepExists_right G (Entails.refl _)

private theorem SepWPp.post_of_entails {prog : Program} {ret : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp} {R : SepProp} {Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P
      (fun sf P' => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ (P' ⊢ Q sf))
      Qp) :
    SepWPp prog ret s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      Qp := by
  intro R' hm hL
  obtain ⟨sf, hsteps, hout⟩ := h R' hm hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hret, hrun, P', hm', hsp, hcs, hent⟩ | hpan
  · exact Or.inl ⟨hret, hrun, P', hm', ⟨fun hmR => Satisfies.mono (sepConj_mono_left hent) hmR, hsp, hcs⟩⟩
  · exact Or.inr hpan

set_option maxHeartbeats 1200000 in
private theorem chainRecvKey_ok_core {extra : Nat} {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hsub_extra : ∀ sp : BitVec 64,
      sp - 128#64 - BitVec.ofNat 64 (extra + nextKeyInternalStackX) =
        sp - BitVec.ofNat 64 (extra + chainRecvKeyStackX))
    (_himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A extra).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr chainRecvKeyName)
      ((chainRecvKeySpecCore hkdf A extra).inImage img) := by
  unfold tripleRatchetProgAtExt
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff chainRecvKeyName = 0x5b4d8 := chainRecvKey_fnOff
  code_fetches libsignalSessionCode libsignalSessionBin img.base (Rust.withPanics ext) hfn 0x5b4d8 1248
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  clear _himg hfn
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x with ⟨out, selfPtr, epoch, index, G, self⟩
  dsimp only [Spec.inImage, chainRecvKeySpecCore] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : ImgCallInv img s0 := ⟨‹img.FrozenLoaded s0›, ‹s0.symtab = img.symtab›⟩
  subst out selfPtr epoch index
  let x0 : ChainRecvKeyGhost :=
    ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), s0.readReg64 (.gpr 2#5),
     (s0.readReg64 (.gpr 3#5)).setWidth 32, G, self⟩
  have h_epi := fun (c3 : BitVec 64) {R0 : SepProp} => @recvKey_epilogue img hkdf A ext x0 s0 c3 R0
  have h_from64 := @recvKey_from_64 extra img hkdf A ext hsub_extra hnextKey hnextKeyPanic hshim halloc hdoRes x0 s0
  dsimp only [x0] at h_epi h_from64
  clear hsub_extra hnextKey hnextKeyPanic hshim halloc hdoRes
  refine SepWPp.rw_pre (by rw [stackAt_chainRecvKeyX_split s0.sp]) ?_
  sep_elim_10 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr chainRecvKeyName = entry_addr
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog_val
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  by_cases hep0 : s0.readReg64 (.gpr 2#5) = 0#64
  · have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = true := by simp [hep0]
    wp_norm_hyp hep_beq
    by_cases hidx0 : (s0.readReg64 (.gpr 3#5)).setWidth 32 = 0#32
    ·
      have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = true := by simp [hidx0]
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = true := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      rw [memRegion_32_ok_split (s0.readReg64 (.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro w0
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w3
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 248#64) hinv0 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      refine SepWP.fold (recvKeyOkAt_empty_intro A (s0.readReg64 (.gpr 0#5))) (by sep_focus) ?_
      refine SepWP.fold (chainAt_entails_chainRepr A (s0.readReg64 (.gpr 1#5)) G self) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
      refine recvKey_frame_extra ?_ (fun {R0} => h_epi c3 (R0 := R0) _ hinv' (by wp_norm_goal))
      rw [hep0, hidx0, recvKey_zero_zero hkdf self]
      dsimp only [recvKeyPostAt]
      sep_frame
    ·
      have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = false := beq_false_of_ne hidx0
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = false := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      refine SepWPp.of_sepWP_inImage (mid := entry_addr + 64#64) hinv0 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyStateInv img s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_
        (h_from64 c3 ‹RecvPrevFits self› (fun ⟨_, hi⟩ => hidx0 hi)
          _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  ·
    have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = false := beq_false_of_ne hep0
    wp_norm_hyp hep_beq
    refine SepWPp.of_sepWP_inImage (mid := entry_addr + 64#64) hinv0 ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyStateInv img s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_from64 c3 ‹RecvPrevFits self› (fun ⟨he, _⟩ => hep0 he)
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

/-- `<spqr::chain::Chain>::recv_key` (`0x608d0`, 312 instructions) meets
`(chainRecvKeySpecX hkdf A).inImage img` given subroutine contracts for its callees. -/
theorem chainRecvKey_ok_of_contracts_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecX hkdf A).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img)) :
    ChainRecvKeyOkX img hkdf A ext := by
  have hnextKey' : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A 0).inImage img) := by
    refine sub_ok_conseq_entails hnextKey (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecRecvCore, nextKeyInternalSpecX]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
    · dsimp only [Spec.inImage, nextKeyInternalSpecRecvCore, nextKeyInternalSpecX]
      rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  unfold ChainRecvKeyOkX
  refine sub_ok_conseq_entails
    (chainRecvKey_ok_core (fun sp => by dsimp only [nextKeyInternalStackX, chainRecvKeyStackX]; bv_kernel)
      himg hnextKey' hnextKeyPanic hshim halloc hdoRes)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainRecvKeySpecCore, chainRecvKeySpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _
  · dsimp only [Spec.inImage, chainRecvKeySpecCore, chainRecvKeySpecX]
    rw [ProofLib.memRegion_zero, emp_sepConj]; exact Entails.refl _

/-- External-hook specialization of `chainRecvKey_ok_of_contracts_x`: given `AllocContractsX`,
`SliceConcat2OkX`, `HkdfToSliceOkX`, and `doReserveSpec`, `<spqr::chain::Chain>::recv_key` meets
`(chainRecvKeySpecX hkdf A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
theorem chainRecvKey_ok_ext_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceOkX img hkdf ext)
    (hA : AllocContractsX img A ext)
    (hdoRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img)) :
    ChainRecvKeyOkX img hkdf A ext :=
  chainRecvKey_ok_of_contracts_x himg
    (nextKeyInternal_ok_ext_x himg hconcat hhkdf hA)
    (nextKeyInternal_panic_ok_ext_x himg)
    (hA.shim extHookStack (by decide) (by decide))
    hA.alloc
    hdoRes

/-- Specialization of `chainRecvKey_ok_ext_x` from `AllocContracts img.base A ext`
(discharging `do_reserve_7_ok_ext` automatically). -/
theorem chainRecvKey_ok_alloc_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceOkX img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainRecvKeyOkX img hkdf A ext :=
  chainRecvKey_ok_ext_x himg hconcat hhkdf
    (AllocContractsX.of_AllocContracts hA)
    (subroutine_ok_inImage_of_subroutine_ok img (do_reserve_7_ok_ext hA))

/-- `<spqr::chain::Chain>::recv_key` (`0x608d0`, 312 instructions) meets
`(chainRecvKeySpecExt hkdf A).inImage img` given contract-parameterized (`*Ext`) subroutine contracts. -/
theorem chainRecvKey_ok_of_contracts_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hnextKey : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecExt hkdf A).inImage img))
    (hnextKeyPanic : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      (nextKeyInternalPanicSpecX.inImage img))
    (hshim : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr shimName)
      ((withStack sessionShimSpec extHookStack).inImage img))
    (halloc : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr allocName)
      ((rustAllocSpecWithStack A extHookStack).inImage img))
    (hdoRes : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img)) :
    ChainRecvKeyOkExt img hkdf A ext := by
  have hnextKey' : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr nextKeyInternalName)
      ((nextKeyInternalSpecRecvCore hkdf A 1232).inImage img) := by
    refine sub_ok_conseq_entails hnextKey (fun x s => ?_) (fun x s0 sf => ?_)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecRecvCore, nextKeyInternalSpecExt]
      rw [stackAt_nextKeyInternalExt_eq s.sp]; exact Entails.of_eq (by ac_rfl)
    · dsimp only [Spec.inImage, nextKeyInternalSpecRecvCore, nextKeyInternalSpecExt]
      rw [stackAt_nextKeyInternalExt_eq s0.sp]; exact Entails.of_eq (by ac_rfl)
  unfold ChainRecvKeyOkExt
  refine sub_ok_conseq_entails
    (chainRecvKey_ok_core (fun sp => by dsimp only [nextKeyInternalStackX, chainRecvKeyStackX]; bv_kernel)
      himg hnextKey' hnextKeyPanic hshim halloc hdoRes)
    (fun x s => ?_) (fun x s0 sf => ?_) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
  · dsimp only [Spec.inImage, chainRecvKeySpecCore, chainRecvKeySpecExt]
    rw [stackAt_chainRecvKeyExt_eq s.sp]; exact Entails.of_eq (by ac_rfl)
  · dsimp only [Spec.inImage, chainRecvKeySpecCore, chainRecvKeySpecExt]
    rw [stackAt_chainRecvKeyExt_eq s0.sp]; exact Entails.of_eq (by ac_rfl)

theorem chainRecvKey_ok_ext_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContractsX img A ext)
    (hdoRes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve7Name)
      ((doReserveSpec A).inImage img)) :
    ChainRecvKeyOkExt img hkdf A ext :=
  chainRecvKey_ok_of_contracts_ext himg
    (nextKeyInternal_ok_ext_ext himg hconcat hhkdf hA)
    (nextKeyInternal_panic_ok_ext_x himg)
    (hA.shim extHookStack (by decide) (by decide))
    hA.alloc
    hdoRes

theorem chainRecvKey_ok_alloc_ext {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img A ext)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainRecvKeyOkExt img hkdf A ext :=
  chainRecvKey_ok_ext_ext himg hconcat hhkdf
    (AllocContractsX.of_AllocContracts hA)
    (subroutine_ok_inImage_of_subroutine_ok img (do_reserve_7_ok_ext hA))

abbrev chainRecvKey_ok_ext := @chainRecvKey_ok_ext_ext

/-! ## Relocatable `[LibsignalPlacement]` Proof (`blkPC_366`) -/

set_option maxHeartbeats 1200000 in
theorem recvKey_from_64_placed [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked)
    (x : ChainRecvKeyGhost) (s0 : State) (c3 : BitVec 64) {R : SepProp}
    (hfits : RecvPrevFits x.self)
    (hne_zero : ¬ (x.epoch = 0#64 ∧ x.index = 0#32))
    (s : State) (hinv : RecvKeyPlacedStateInv lsmpl s0 s)
    (hpc : s.pc = (blkPl_366).base + 64#64)
    (hx1 : s.readReg64 (.gpr 1#5) = x.selfPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = x.epoch)
    (hx19 : s.readReg64 (.gpr 19#5) = x.out)
    (hw20 : (s.readReg64 (.gpr 20#5)).setWidth 32 = x.index) :
    let prog := (blkPC_366).rebase (blkPl_366).base H
    SepWPp prog (s0.readReg64 (.gpr 30#5)) s
      (memRegion x.out 32 ∗
        chainAt A x.selfPtr x.G x.self ∗
        stackAt (s0.sp - 128#64) nextKeyInternalStackX ∗
        memRegion (s0.sp - 120#64) 36 ∗
        recvKeyFrameRestAt s0 c3 ∗
        A.pool)
      (recvKeyPost hkdf A x s0)
      (recvKeyPanic hkdf A x s0 R) := by
  intro prog
  have h_err228 := @recvKey_err_epochOutOfRange_from_228_placed _ hkdf A H x s0 c3 R
  have h_err880 := @recvKey_err_keyAlreadyRequested_from_880_placed _ hkdf A H x s0 c3 R
  have h_err204 := @recvKey_err_keyJump_from_204_placed _ hkdf A H x s0 c3 R
  have h_get276 := @recvKey_get_from_276_placed _ hkdf A H hshim halloc hoom_ext hassert_ext hadd_ext x s0 c3 R
  have h_adv360 := @recvKey_advance_from_360_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hdoRes
    hoom_ext hslice_ext hpanic_ext hadd_ext x s0 c3 R
  clear hnextKey hnextKeyPanic hshim halloc hdoRes hoom_ext hassert_ext hadd_ext hslice_ext hpanic_ext
  dsimp only [prog]; clear prog
  refine SepWPp.fold (chainAt_unpack_sendKey A x.selfPtr x.G x.self) (by sep_focus) ?_
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hlen_eq, hlen_le, hcap_lt, hptr⟩
  have hsp_align := hinv.spAligned
  rcases hinv with ⟨hF, hrun, hsp, hsp0_align, hx26, hx27, hx28, htrace, hvregs⟩
  wp_norm_hyp hx26; wp_norm_hyp hx27; wp_norm_hyp hx28; wp_norm_hyp hvregs
  wp_norm_hyp hrun; wp_norm_hyp hsp_align; wp_norm_hyp hsp
  wp_norm_hyp hx1; wp_norm_hyp hx2; wp_norm_hyp hx19; wp_norm_hyp hw20; wp_norm_hyp htrace
  by_cases hgt_curr : x.epoch > x.self.currentEpoch
  · have ⟨hult_curr, hule_curr⟩ := lt64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 228#64) hF ?_
    wp_steps
    refine SepWP.fold (chainRepr_pack_sendKey A x.selfPtr x.G x.self
      x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
    have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
      recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero (epochIdx_of_gt x.self x.epoch hgt_curr)
    refine SepWPp.mono_pre _ ?_
      (h_err228 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame
  · have ⟨hult_curr, hule_curr⟩ := ge64_props hgt_curr
    wp_norm_hyp hult_curr; wp_norm_hyp hule_curr
    by_cases hback_ge : (x.self.currentEpoch - x.epoch).toNat ≥ x.self.links.length
    · have ⟨hult_back, hule_back⟩ := back_ge64_props hback_ge (by omega : x.self.links.length < 2 ^ 63)
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 228#64) hF ?_
      wp_steps
      refine SepWP.fold (chainRepr_pack_sendKey A x.selfPtr x.G x.self
        x.G.linksHead x.G.epochs x.self.links x.self.sendEpoch hlen_eq) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
      have hres_err : Chain.recvKey hkdf x.self x.epoch x.index = .error (.err (.epochOutOfRange x.epoch)) :=
        recvKey_of_epochIdx_err hkdf x.self x.epoch x.index _ hne_zero
          (epochIdx_of_back_ge x.self x.epoch hgt_curr hback_ge)
      refine SepWPp.mono_pre _ ?_
        (h_err228 hres_err _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
    · have hback_lt : (x.self.currentEpoch - x.epoch).toNat < x.self.links.length := by omega
      have hlen_lt63 : x.self.links.length < 2 ^ 63 := by omega
      have ⟨hult_back, hule_back⟩ := back_lt64_props hback_lt hlen_lt63
      have ⟨hult_nb, hule_nb⟩ := back_add_not_no_borrow hback_lt hlen_lt63
      let epochIndex := x.self.links.length - 1 - (x.self.currentEpoch - x.epoch).toNat
      have hi_ep : epochIndex < x.self.links.length := by dsimp [epochIndex]; omega
      have hidx_eq : x.self.epochIdx x.epoch = .ok epochIndex :=
        epochIdx_of_lt x.self x.epoch hgt_curr hback_lt
      have hadd_not :
          BitVec.ofNat 64 x.self.links.length + ~~~(x.self.currentEpoch - x.epoch) =
            BitVec.ofNat 64 epochIndex :=
        add_not_eq_ofNat_sub hback_lt
      have hzip_le : (x.G.epochs.zip x.self.links).length ≤ x.G.linksCap.toNat := by simp [hlen_eq, hlen_le]
      have hzip_i : epochIndex < (x.G.epochs.zip x.self.links).length := by simp [hlen_eq, hi_ep]
      refine SepWPp.fold
        (vecDequeRingBuf_get_physIdx A x.G.linksCap x.G.linksPtr x.G.linksHead
          (x.G.epochs.zip x.self.links) hzip_le hzip_i) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hhead, _, _⟩
      have hzip_geti : (x.G.epochs.zip x.self.links)[epochIndex] =
          (x.G.epochs[epochIndex]'(by omega), x.self.links[epochIndex]'hi_ep) := by
        simp [List.getElem_zip]
      rw [hzip_geti]
      let gce := x.G.epochs[epochIndex]'(by omega)
      let link := x.self.links[epochIndex]'hi_ep
      let s_idx := vecDequePhysIdx x.G.linksHead.toNat x.G.linksCap.toNat epochIndex
      let epPtr := x.G.linksPtr + BitVec.ofNat 64 (s_idx * 112)
      refine SepWPp.fold (chainEpochAt_unpack_recv A gce epPtr link) (by sep_focus) ?_
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hn_le, hn_cap, hn_ptr, hp_le, hp_cap, hp_ptr⟩
      refine SepWPp.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self)) (by sep_focus) ?_
      have hmadd := physIdx_madd_eq (ptr := x.G.linksPtr) hhead (Nat.lt_of_lt_of_le hi_ep hlen_le) hcap_lt
      have hres_ep : Chain.recvKey hkdf x.self x.epoch x.index = (do
          let (recv', out) ← link.recv.key hkdf x.index x.self.params
          let links' := x.self.links.set epochIndex { link with recv := recv' }
          return ({ x.self with links := links' }, out)) :=
        recvKey_of_epochIdx_ok hkdf x.self x.epoch x.index epochIndex link hne_zero hidx_eq
          (List.getElem?_eq_getElem hi_ep)
      have hult_ei : (BitVec.ofNat 64 epochIndex).ult (BitVec.ofNat 64 x.self.links.length) = true :=
        hadd_not ▸ hult_nb
      have hule_ei : (BitVec.ofNat 64 x.self.links.length).ule (BitVec.ofNat 64 epochIndex) = false :=
        hadd_not ▸ hule_nb
      wp_norm_hyp hult_back; wp_norm_hyp hule_back
      wp_norm_hyp hult_nb; wp_norm_hyp hule_nb
      wp_norm_hyp hadd_not; wp_norm_hyp hult_ei; wp_norm_hyp hule_ei; wp_norm_hyp hmadd
      by_cases heq_ctr : x.index = link.recv.ctr
      · have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_eq_props heq_ctr
        wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
        wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
        refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 880#64) hF ?_
        wp_steps
        refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
          link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
        refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
          link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
        have hpack := chainRepr_pack_recv A x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
          hhead hcap_lt hptr hlen_le hlen_eq
        dsimp only [s_idx, epPtr, link] at hpack ⊢
        have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
            x.self.links := List.set_getElem_self hi_ep
        rw [hset_self] at hpack
        refine SepWP.fold hpack (by sep_focus) ?_
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hF'
        have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
          ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
        have hres_already : Chain.recvKey hkdf x.self x.epoch x.index =
            .error (.err (.keyAlreadyRequested x.index)) := by
          rw [hres_ep, ced_key_of_eq hkdf link.recv x.index x.self.params heq_ctr]
          rfl
        refine SepWPp.mono_pre _ ?_
          (h_err880 hres_already _ hinv'
            (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
        sep_frame
      · by_cases hlt_ctr : x.index < link.recv.ctr
        · have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_lt_props hlt_ctr
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 276#64) hF ?_
          wp_steps
          refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
            link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
          refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
            link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          intro hF'
          have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
            ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
             by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
          have hres_get : Chain.recvKey hkdf x.self x.epoch x.index = (do
              let recv := (x.self.links[epochIndex]'hi_ep).recv
              let (prev', outKey) ← recv.prev.get x.index recv.ctr x.self.params
              let recv' := { recv with prev := prev' }
              let links' := x.self.links.set epochIndex { x.self.links[epochIndex]'hi_ep with recv := recv' }
              return ({ x.self with links := links' }, outKey)) := by
            rw [hres_ep, ced_key_of_lt hkdf link.recv x.index x.self.params hlt_ctr]
            dsimp only [link]
            cases (x.self.links[epochIndex]'hi_ep).recv.prev.get x.index (x.self.links[epochIndex]'hi_ep).recv.ctr x.self.params <;> rfl
          refine SepWPp.mono_pre _ ?_
            (h_get276 epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq hres_get
              _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
              (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
          unfold chainOuterRecvAt
          dsimp only [s_idx, epPtr, link, gce]
          sep_frame
        · have hgt_ctr : link.recv.ctr < x.index := by
            apply BitVec.lt_def.mpr
            have h1 : ¬ (x.index.toNat < link.recv.ctr.toNat) := fun h => hlt_ctr (BitVec.lt_def.mpr h)
            have h2 : x.index.toNat ≠ link.recv.ctr.toNat := fun h => heq_ctr (BitVec.eq_of_toNat_eq h)
            omega
          have ⟨hult1, hult2, hule1, hule2, hbeq_c, hsub_c⟩ := cmp32_gt_props hgt_ctr
          have ⟨hmaxJ1, hmaxJ2⟩ := maxJumpOrDefault_csel_eq x.self.params
          have ⟨hult_jmp, hule_jmp⟩ := jump_cmp_props x.index link.recv.ctr x.self.params
          wp_norm_hyp hult1; wp_norm_hyp hult2; wp_norm_hyp hule1; wp_norm_hyp hule2
          wp_norm_hyp hbeq_c; wp_norm_hyp hsub_c
          wp_norm_hyp hmaxJ1; wp_norm_hyp hmaxJ2
          wp_norm_hyp hult_jmp; wp_norm_hyp hule_jmp
          by_cases hjump : x.index - link.recv.ctr > x.self.params.maxJumpOrDefault
          · have hjump_t : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = true :=
              decide_eq_true hjump
            wp_norm_hyp hjump_t
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 204#64) hF ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x38#64) gce.recv.next.cap gce.recv.next.ptr
              link.recv.next hn_le hn_cap hn_ptr) (by sep_focus) ?_
            refine SepWP.fold (vecU8At_pack_prev A (epPtr + 0x50#64) gce.recv.prev.cap gce.recv.prev.ptr
              link.recv.prev.data hp_le hp_cap hp_ptr) (by sep_focus) ?_
            have hpack := chainRepr_pack_recv A x.selfPtr x.G x.self epochIndex hi_ep gce gce.recv.prev link.recv
              hhead hcap_lt hptr hlen_le hlen_eq
            dsimp only [s_idx, epPtr, link] at hpack ⊢
            have hset_self : x.self.links.set epochIndex { x.self.links[epochIndex] with recv := (x.self.links[epochIndex]).recv } =
                x.self.links := List.set_getElem_self hi_ep
            rw [hset_self] at hpack
            refine SepWP.fold hpack (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
            have hres_jmp : Chain.recvKey hkdf x.self x.epoch x.index =
                .error (.err (.keyJump link.recv.ctr x.index)) := by
              rw [hres_ep, ced_key_of_gt_jump hkdf link.recv x.index x.self.params hgt_ctr hjump]
              rfl
            refine SepWPp.mono_pre _ ?_
              (h_err204 link.recv.ctr hres_jmp _ hinv' (by wp_norm_goal)
                (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            sep_frame
          · have hjump_f : decide (x.index - link.recv.ctr > x.self.params.maxJumpOrDefault) = false :=
              decide_eq_false hjump
            wp_norm_hyp hjump_f
            refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 360#64) hF ?_
            wp_steps
            refine SepWP.fold (Entails.of_eq (chainRestSendKeyAt_params_eq A x.selfPtr x.G x.self).symm) (by sep_focus) ?_
            apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            intro hF'
            have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
              ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
               by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, htrace, by wp_norm_goal⟩
            have hp_fit0 : (x.self.links[epochIndex]'hi_ep).recv.prev.data.length < 2 ^ 61 :=
              hfits _ (List.getElem_mem hi_ep)
            refine SepWPp.mono_pre _ ?_
              (h_adv360 epochIndex hi_ep gce hhead hcap_lt hptr hlen_le hlen_eq
                hn_le hn_cap hn_ptr hp_le hp_cap hp_ptr hp_fit0 hgt_ctr hjump hres_ep
                _ hinv' (by wp_norm_goal) (by dsimp only [link]; wp_norm_goal) (by wp_norm_goal)
                (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
            unfold chainOuterRecvAt
            dsimp only [s_idx, epPtr, link, gce]
            sep_frame

set_option maxHeartbeats 1200000 in
theorem chainRecvKey_placed_ok_of_contracts [LibsignalPlacement] {hkdf : HkdfFn} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hnextKey : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX hkdf A)))
    (hnextKeyPanic : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX))
    (hshim : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec extHookStack))
    (halloc : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack A extHookStack))
    (hdoRes : subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec A)))
    (hoom_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (hassert_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_") = some Rust.panicked)
    (hadd_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow") = some Rust.panicked)
    (hslice_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail") = some Rust.panicked)
    (hpanic_ext : ((blkPC_366).rebase (blkPl_366).base H).externAt?
      (lsρ "_RNvNtCskxtBwYRO61I_4core9panicking5panic") = some Rust.panicked) :
    ChainRecvKeyPlacedOkX hkdf A H := by
  unfold ChainRecvKeyPlacedOkX
  wpp_init x s0
  have hsp0_align : s0.spAligned = true := hsp_align
  rcases x with ⟨out, selfPtr, epoch, index, G, self⟩
  dsimp only [withLsCallInv, chainRecvKeySpecX] at *
  refine SepWPp.post_of_entails ?_
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨‹LibsignalRoLoaded lsmpl s0.mem›, ‹LibsignalCodeLoaded lsmpl s0.mem›⟩
  subst out selfPtr epoch index
  let x0 : ChainRecvKeyGhost :=
    ⟨s0.readReg64 (.gpr 0#5), s0.readReg64 (.gpr 1#5), s0.readReg64 (.gpr 2#5),
     (s0.readReg64 (.gpr 3#5)).setWidth 32, G, self⟩
  have h_epi := @recvKey_epilogue_placed _ hkdf A H x0 s0
  have h_from64 := @recvKey_from_64_placed _ hkdf A H hnextKey hnextKeyPanic hshim halloc hdoRes
    hoom_ext hassert_ext hadd_ext hslice_ext hpanic_ext x0 s0
  dsimp only [x0] at h_epi h_from64
  clear hnextKey hnextKeyPanic hshim halloc hdoRes hoom_ext hassert_ext hadd_ext hslice_ext hpanic_ext
  refine SepWPp.rw_pre (by rw [stackAt_chainRecvKeyX_split s0.sp]) ?_
  sep_elim_10 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  by_cases hep0 : s0.readReg64 (.gpr 2#5) = 0#64
  · have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = true := by simp [hep0]
    wp_norm_hyp hep_beq
    by_cases hidx0 : (s0.readReg64 (.gpr 3#5)).setWidth 32 = 0#32
    · have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = true := by simp [hidx0]
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = true := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      rw [memRegion_32_ok_split (s0.readReg64 (.gpr 0#5))]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWPp.exists_elim; intro w0
      apply SepWPp.exists_elim; intro w1
      apply SepWPp.exists_elim; intro w2
      apply SepWPp.exists_elim; intro w3
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 248#64) hinv0 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      refine SepWP.fold (recvKeyOkAt_empty_intro A (s0.readReg64 (.gpr 0#5))) (by sep_focus) ?_
      refine SepWP.fold (chainAt_entails_chainRepr A (s0.readReg64 (.gpr 1#5)) G self) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_ (h_epi c3 _ hinv' (by wp_norm_goal))
      rw [hep0, hidx0, recvKey_zero_zero hkdf self]
      dsimp only [recvKeyPostAt]
      sep_frame
    · have hidx_beq : ((s0.readReg64 (.gpr 3#5)).setWidth 32 == 0#32) = false := beq_false_of_ne hidx0
      have hidx_zext : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s0.readReg64 (.gpr 3#5))) == 0#64) = false := by
        rw [zeroExtend64_truncate32_beq_zero]; exact hidx_beq
      wp_norm_hyp hidx_beq; wp_norm_hyp hidx_zext
      refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 64#64) hinv0 ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hF'
      have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
        ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
         by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
      refine SepWPp.mono_pre _ ?_
        (h_from64 c3 ‹RecvPrevFits self› (fun ⟨_, hi⟩ => hidx0 hi)
          _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
      sep_frame
  · have hep_beq : (s0.readReg64 (.gpr 2#5) == 0#64) = false := beq_false_of_ne hep0
    wp_norm_hyp hep_beq
    refine SepWPp.of_sepWP_lsCallInv (mid := (blkPl_366).base + 64#64) hinv0 ?_
    wp_steps
    refine SepWP.fold (Entails.of_eq (recvKeyFrameRestAt_def s0 c3).symm) (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hF'
    have hinv' : RecvKeyPlacedStateInv lsmpl s0 _ :=
      ⟨hF', by wp_norm_goal, by wp_norm_goal, hsp0_align,
       by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, rfl, by wp_norm_goal⟩
    refine SepWPp.mono_pre _ ?_
      (h_from64 c3 ‹RecvPrevFits self› (fun ⟨he, _⟩ => hep0 he)
        _ hinv' (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal))
    sep_frame

abbrev chainRecvKey_placed_ok := @chainRecvKey_placed_ok_of_contracts

end CryptoVerification.SpqrV1.ChainProofs
