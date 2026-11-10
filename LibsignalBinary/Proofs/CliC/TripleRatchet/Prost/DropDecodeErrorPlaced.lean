/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.CliC.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Proof of `CliC` `drop_glue<DecodeError> [local#3]`

Proves `[LibsignalPlacement]` contracts (`dropDecodeErrorSpec` and `dropDecodeErrorSpecX`) for
`CliC` `core::ptr::drop_glue::<prost::error::DecodeError> [local#3]` (Block `555`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Prost

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession
open CryptoVerification.RecordCodecs.Placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_placed_ok_gen
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks} {dStack : Nat}
    (hd : 0x20 + dStack ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok (lsProg_551 H) (lsρ lsRustDeallocSymCli)
      (rustDeallocExternSpecWithStack A dStack)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorSpecGen A dStack) := by
  simp only [dropDecodeErrorSpecGen, decodeErrorAt, decodeErrorAtStackLen, vecOf, vecAt,
    vecHeader, vecBuf, stackAt_dropDecodeErrorGen hd, sepExists_sepConj_left, sepExists_sepConj_right,
    List.length_replicate]
  simp only [rustDeallocExternSpecWithStack] at hdealloc
  wp_init e s0
  have hkv : KindNoHeap v_stk_5 := by assumption
  have hbr := kindNoHeap_branch_false hkv
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have h_len_le : v_stk_4 ≤ v_stk_6.toNat := by assumption
  have h_cap_lt : v_stk_6.toNat * 32 < 2 ^ 63 := by assumption
  by_cases hcap0 : v_stk_6 = 0
  · subst hcap0
    simp only [ite_true, emp_sepConj]
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e 0 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done
  · have hcap_beq : (v_stk_6 == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    have hshl : (v_stk_6 <<< 5).toNat = v_stk_6.toNat * 32 := shl5_toNat h_cap_lt
    have hlay_vec : LayoutOk (v_stk_6.toNat * 32) 8 := layoutOk_mul32_8 hcap0 h_cap_lt
    have hpos_vec : 0 < v_stk_6.toNat * 32 := hlay_vec.1
    have hsum_vec : v_stk_6.toNat * 32 + 8 ≤ 2 ^ 63 := hlay_vec.2.2
    simp only [hcap0, ite_false, stackVec_buf_memRegion h_len_le h_cap_lt]
    wp_steps
    wp_call hdealloc (v_stk_7, v_stk_6.toNat * 32, 8)
    wp_steps
    apply SepWP.fold (box72_entails_memRegion e v_stk_6 v_stk_7 (BitVec.ofNat 64 v_stk_4) v_stk_5)
      (by sep_focus)
    apply SepWP.fold (stackAt_dropDecodeErrorGen_tail hd s0.sp _ _ _ _) (by sep_focus)
    wp_call hdealloc (e, 72, 8)
    apply SepWP.fold (Entails.of_eq (stackAt_dropDecodeErrorGen_post hd s0.sp)) (by sep_focus)
    wp_done

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_placed_ok
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSymCli (rustDeallocSpec A)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorSpec A) := by
  refine CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_placed_ok_gen
    (dStack := allocHookStack) (by decide) ?_
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem (a := lsRustDeallocSymCli)
    (l := libsignalSessionExterns) (by decide)
  exact rustDeallocExternWithStack_of_rustDealloc
    (ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hdealloc)

theorem _root_.CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_placed_ok_x
    [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSymCli (rustDeallocSpec A)) :
    subroutine_ok (lsProg_551 H) (blkPl_551).base
      (dropDecodeErrorSpecX A) := by
  refine CryptoVerification.CliC.LibsignalTripleRatchet.Prost.dropDecodeError_placed_ok_gen
    (dStack := extHookStack) (by decide) ?_
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem (a := lsRustDeallocSymCli)
    (l := libsignalSessionExterns) (by decide)
  exact rustDeallocExternWithStack_of_rustDealloc
    (ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) hdealloc)
    (by decide) (by decide)

end CryptoVerification.LibsignalTripleRatchet.Prost
