/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Relocatable, Block `338`)

Relocatable `[LibsignalPlacement]` proofs on `lsProg_338 (Rust.withPanics ext)` (`99` instructions):
`unchunked_ct1_sent_recv_ek_placed_ok_x` and `unchunked_ct1_sent_recv_ek_placed_cl_ok_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

private def deallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"
private def validatePkSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes"

private theorem unchunked_recv_ek_epilogue_ret_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (outA stA ekA : BitVec 64)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (w8 : BitVec 64)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_338).base + 344#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      unchunkedCt1SentRecvEkResAt A outA res ∗
      memRegion stA 128 ∗
      memRegion ekA 24 ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) extHookStack ∗
      memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
            unchunkedCt1SentRecvEkResAt A outA res ∗
            memRegion stA 128 ∗
            memRegion ekA 24 ∗
            A.pool ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  subst hP
  wp_conv_pre => unfold unchunkedRecvEkSavedCells
  wp_steps
  refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
  refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 w8) (by sep_focus) ?_
  wp_done

private theorem unchunked_recv_ek_tail_dealloc_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_call : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (outA stA ekA cap ptr : BitVec 64)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (w8 : BitVec 64)
    (hcap_ne : cap ≠ 0#64)
    (hcap_lt : cap.toNat < 2 ^ 63)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_338).base + 316#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 208#64)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      unchunkedCt1SentRecvEkResAt A outA res ∗
      memRegion stA 128 ∗
      memRegion ekA 24 ∗
      A.live ptr cap.toNat 1 ∗
      memRegion ptr cap.toNat ∗
      A.pool ∗
      stackAt (s0.sp - 208#64) extHookStack ∗
      memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ w8) ∗
      memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗
            unchunkedCt1SentRecvEkResAt A outA res ∗
            memRegion stA 128 ∗
            memRegion ekA 24 ∗
            A.pool ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  simp only [rustDeallocSpec] at hdealloc_call
  subst hP
  have hlay : LayoutOk cap.toNat 1 :=
    ⟨Nat.pos_of_ne_zero (fun h => hcap_ne (BitVec.eq_of_toNat_eq h)),
     ⟨0, rfl⟩,
     by omega⟩
  wp_conv_pre => unfold unchunkedRecvEkSavedCells
  wp_steps
  refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
  refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 w8) (by sep_focus) ?_
  wp_conv_pre => rw [stackAt_unchunkedRecvEk_tail_split s0.sp]
  wp_apply
  refine SepWP.fold (Entails.of_eq (stackAt_unchunkedRecvEk_tail_split s0.sp).symm) (by sep_focus) ?_
  wp_done

private theorem unchunked_recv_ek_ok_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_call : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (outA stA ekA hdrCap hdrPtr ekCap ekPtr : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (hres : res = .ok { epoch := st.epoch, auth := st.auth, es := st.es, ek := ek, ct1 := st.ct1 })
    (hhdr_le : st.hdr.length ≤ hdrCap.toNat) (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hek_le : ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63) (hek_ne : ekPtr ≠ 0#64)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_338).base + 220#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 .x19 = stA) (hx20 : s.readReg64 .x20 = hdrPtr)
    (hx21 : s.readReg64 .x21 = outA) (hx22 : s.readReg64 .x22 = st.epoch)
    (hx23 : s.readReg64 .x23 = ekA)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 128 ∗ authenticatorAt A stA st.auth ∗
      ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗
      ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.hdr.length) ∗
      (hdrPtr ↦ₛ st.hdr) ∗ vecU8Tail A hdrCap hdrPtr st.hdr ∗
      vecU8 A (stA + 72#64) st.es ∗ vecU8 A (stA + 96#64) st.ct1 ∗
      ((stA + 120#64) ↦₆₄ st.epoch) ∗
      (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗
      ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek ∗ A.pool ∗
      stackAt (s0.sp - 208#64) extHookStack ∗ memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  simp only [rustDeallocSpec] at hdealloc_call
  subst hP
  have hauth_eq : authenticatorAt A stA st.auth =
      (vecU8 A stA st.auth.rootKey ∗ vecU8 A (stA + 24#64) st.auth.macKey) := rfl
  wp_conv_pre => rw [hauth_eq]
  refine SepWP.fold (vecU8_unfold_body A stA st.auth.rootKey) (by sep_focus) ?_
  wp_pull_exists; rename_i rkCap rkPtr
  refine SepWP.fold (vecU8_unfold_body_24 A stA st.auth.macKey) (by sep_focus) ?_
  wp_pull_exists; rename_i mkCap mkPtr
  refine SepWP.fold (vecU8_unfold_body_72 A stA st.es) (by sep_focus) ?_
  wp_pull_exists; rename_i esCap esPtr
  refine SepWP.fold (vecU8_unfold_body_96 A stA st.ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i ct1Cap ct1Ptr
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A hdrCap hdrPtr st.hdr hhdr_le hhdr_lt)
    (by sep_focus) ?_
  refine SepWP.fold (cells_16_unfold outA) (by sep_focus) ?_
  wp_pull_exists
  refine SepWP.fold (cells_16_unfold (s0.sp - 192#64)) (by sep_focus) ?_
  wp_pull_exists
  wp_conv_pre => simp only [wordsAt_16, arm64_norm]
  wp_steps
  have hfold_out :
      (outA ↦₆₄ rkCap) ∗ ((outA + 8#64) ↦₆₄ rkPtr) ∗ ((outA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
      vecU8Body A rkCap rkPtr st.auth.rootKey ∗
      ((outA + 24#64) ↦₆₄ mkCap) ∗ ((outA + 32#64) ↦₆₄ mkPtr) ∗ ((outA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
      vecU8Body A mkCap mkPtr st.auth.macKey ∗
      ((outA + 48#64) ↦₆₄ esCap) ∗ ((outA + 56#64) ↦₆₄ esPtr) ∗ ((outA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
      vecU8Body A esCap esPtr st.es ∗
      ((outA + 72#64) ↦₆₄ ekCap) ∗ ((outA + 80#64) ↦₆₄ ekPtr) ∗ ((outA + 88#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek ∗
      ((outA + 96#64) ↦₆₄ ct1Cap) ∗ ((outA + 104#64) ↦₆₄ ct1Ptr) ∗ ((outA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
      vecU8Body A ct1Cap ct1Ptr st.ct1 ∗
      ((outA + 120#64) ↦₆₄ st.epoch) ⊢
      unchunkedCt1SentRecvEkResAt A outA res := by
    rw [hres]
    exact fold_unchunkedCt1SentEkReceivedAt A outA st ek
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr hek_le hek_lt hek_ne
  refine SepWP.fold hfold_out (by sep_focus) ?_
  refine SepWP.fold (words16_entails_memRegion_128 stA
      rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
      hdrCap hdrPtr (BitVec.ofNat 64 st.hdr.length)
      esCap esPtr (BitVec.ofNat 64 st.es.length)
      ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) st.epoch)
    (by sep_focus) ?_
  refine SepWP.fold (words3_entails_memRegion_24 ekA ekCap ekPtr (BitVec.ofNat 64 ek.length))
    (by sep_focus) ?_
  refine SepWP.fold (words16_sub192_entails_memRegion_128 s0.sp
      rkCap rkPtr (BitVec.ofNat 64 st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 st.auth.macKey.length)
      esCap esPtr (BitVec.ofNat 64 st.es.length)
      ekCap ekPtr (BitVec.ofNat 64 ek.length)
      ct1Cap ct1Ptr (BitVec.ofNat 64 st.ct1.length) _)
    (by sep_focus) ?_
  wp_conv_pre => unfold unchunkedRecvEkSavedCells
  dsimp only [vecCapPtrDealloc]
  by_cases hhdr0 : (hdrCap == 0#64) = true <;>
    simp only [hhdr0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
    refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 st.epoch) (by sep_focus) ?_
    wp_done
  · have hhdr_ne : hdrCap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hhdr0)
    have hlay : LayoutOk hdrCap.toNat 1 :=
      ⟨Nat.pos_of_ne_zero (fun h => hhdr_ne (BitVec.eq_of_toNat_eq h)), ⟨0, rfl⟩, by omega⟩
    wp_steps
    refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
    refine SepWP.fold (stackAt_unchunkedRecvEk_restore s0 st.epoch) (by sep_focus) ?_
    wp_conv_pre => rw [stackAt_unchunkedRecvEk_tail_split s0.sp]
    wp_apply
    refine SepWP.fold (Entails.of_eq (stackAt_unchunkedRecvEk_tail_split s0.sp).symm) (by sep_focus) ?_
    wp_done

private theorem unchunked_recv_ek_err_branch_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc_call : subroutine_ok ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (outA stA ekA hdrCap hdrPtr ekCap ekPtr : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) (ek : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (hres : res = .error .erroneousDataReceived)
    (hhdr_le : st.hdr.length ≤ hdrCap.toNat) (hhdr_lt : hdrCap.toNat < 2 ^ 63)
    (hek_le : ek.length ≤ ekCap.toNat) (hek_lt : ekCap.toNat < 2 ^ 63)
    {s0 s : State} {P : SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_338).base + 88#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 208#64)
    (hx19 : s.readReg64 .x19 = stA) (hx20 : s.readReg64 .x20 = hdrPtr)
    (hx21 : s.readReg64 .x21 = outA) (hx23 : s.readReg64 .x23 = ekA)
    (hx24 : s.readReg64 .x24 = ekPtr)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (
      memRegion outA 128 ∗ authenticatorAt A stA st.auth ∗
      ((stA + 48#64) ↦₆₄ hdrCap) ∗ ((stA + 56#64) ↦₆₄ hdrPtr) ∗
      ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.hdr.length) ∗
      (hdrPtr ↦ₛ st.hdr) ∗ vecU8Tail A hdrCap hdrPtr st.hdr ∗
      vecU8 A (stA + 72#64) st.es ∗ vecU8 A (stA + 96#64) st.ct1 ∗
      ((stA + 120#64) ↦₆₄ st.epoch) ∗
      (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗
      ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
      (ekPtr ↦ₛ ek) ∗ vecU8Tail A ekCap ekPtr ek ∗ A.pool ∗
      stackAt (s0.sp - 208#64) extHookStack ∗ memRegion (s0.sp - 208#64) 8 ∗
      ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
      unchunkedRecvEkSavedCells s0)) :
    SepWP ((blkPC_338).rebase (blkPl_338).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s P
      (fun sf P_f =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
          (P_f ⊢ ⌜sf.trace = s0.trace⌝ ∗ unchunkedCt1SentRecvEkResAt A outA res ∗
            memRegion stA 128 ∗ memRegion ekA 24 ∗
            A.pool ∗ stackAt s0.sp unchunkedRecvEkStack)) := by
  have hdealloc_raw := hdealloc_call
  simp only [rustDeallocSpec] at hdealloc_raw
  have h_epilogue := @unchunked_recv_ek_epilogue_ret_placed _ A F ext
  have h_tail := unchunked_recv_ek_tail_dealloc_placed (F := F) hdealloc_call
  subst hP
  have hauth_eq : authenticatorAt A stA st.auth =
      (vecU8 A stA st.auth.rootKey ∗ vecU8 A (stA + 24#64) st.auth.macKey) := rfl
  wp_conv_pre => rw [hauth_eq, stackAt_sub208_extHook_split s0.sp]
  refine SepWP.fold (memRegion_128_unfold_err outA) (by sep_focus) ?_
  wp_pull_exists; rename_i outW0 outB8
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound A stA st.auth.rootKey) (by sep_focus) ?_
  wp_pull_exists; rename_i rkCap rkPtr
  wp_focus_pure; intro hrk_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_24 A stA st.auth.macKey) (by sep_focus) ?_
  wp_pull_exists; rename_i mkCap mkPtr
  wp_focus_pure; intro hmk_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_72 A stA st.es) (by sep_focus) ?_
  wp_pull_exists; rename_i esCap esPtr
  wp_focus_pure; intro hes_lt
  refine SepWP.fold (vecU8_entails_capPtr_dealloc_bound_96 A stA st.ct1) (by sep_focus) ?_
  wp_pull_exists; rename_i ct1Cap ct1Ptr
  wp_focus_pure; intro hct1_lt
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A hdrCap hdrPtr st.hdr hhdr_le hhdr_lt)
    (by sep_focus) ?_
  refine SepWP.fold (slice_and_tail_entails_vecCapPtrDealloc A ekCap ekPtr ek hek_le hek_lt)
    (by sep_focus) ?_
  refine SepWP.fold (fold_fiveVec128HeadersAt_err stA
      rkCap rkPtr mkCap mkPtr hdrCap hdrPtr (BitVec.ofNat 64 st.hdr.length)
      esCap esPtr ct1Cap ct1Ptr st.epoch)
    (by sep_focus) ?_
  let g : FiveVecGhost :=
    ⟨⟨rkCap, rkPtr⟩, ⟨mkCap, mkPtr⟩, ⟨hdrCap, hdrPtr⟩, ⟨esCap, esPtr⟩, ⟨ct1Cap, ct1Ptr⟩⟩
  refine Drop.seq_clean (mid := (blkPl_338).base + 124#64)
    (P_mid := (fiveVec128HeadersAt stA g ∗
      vecCapPtrDealloc A rkCap rkPtr ∗ vecCapPtrDealloc A mkCap mkPtr ∗
      vecCapPtrDealloc A hdrCap hdrPtr ∗ vecCapPtrDealloc A esCap esPtr ∗
      vecCapPtrDealloc A ct1Cap ct1Ptr) ∗
      A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ errBranchFrame A outA ekA res s0 st.epoch)
    (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
  · wp_step; wp_step; wp_step; wp_step; wp_step
    have hfold_err :
        (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 119 ∗
        (ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗ ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length) ∗
        memRegion (s0.sp - 16592#64) 12288 ∗ memRegion (s0.sp - 208#64) 8 ∗
        ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
        unchunkedRecvEkSavedCells s0 ⊢
        errBranchFrame A outA ekA res s0 st.epoch := by
      unfold errBranchFrame; rw [hres]; dsimp only [unchunkedCt1SentRecvEkResAt]
      have hek24 := words3_entails_memRegion_24 ekA ekCap ekPtr (BitVec.ofNat 64 ek.length)
      refine Entails.trans (Entails.of_eq (show _ =
        (((ekA ↦₆₄ ekCap) ∗ ((ekA + 8#64) ↦₆₄ ekPtr) ∗ ((ekA + 16#64) ↦₆₄ BitVec.ofNat 64 ek.length)) ∗
         ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 119 ∗
          memRegion (s0.sp - 16592#64) 12288 ∗ memRegion (s0.sp - 208#64) 8 ∗
          ((s0.sp - 200#64) ↦₆₄ st.epoch) ∗ memRegion (s0.sp - 192#64) 128 ∗
          unchunkedRecvEkSavedCells s0)) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hek24) ?_
      exact Entails.of_eq (by ac_rfl)
    refine SepWP.fold hfold_err (by dsimp only [noneCap]; sep_focus) ?_
    dsimp only [vecCapPtrDealloc]
    by_cases hek0 : (ekCap == 0#64) = true <;>
      simp only [hek0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
    · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, hx19_1, hx20_1, hx25_1, hx26_1, hx27_1, hx28_1, htr1, hvregs_1⟩
    refine Drop.seq_clean (mid := (blkPl_338).base + 144#64)
      (P_mid := (fiveVec128HeadersAt stA g ∗
        vecCapPtrDealloc A mkCap mkPtr ∗ vecCapPtrDealloc A hdrCap hdrPtr ∗
        vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr) ∗
        A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ errBranchFrame A outA ekA res s0 st.epoch)
      (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
    · dsimp only [fiveVec128HeadersAt, g, vecCapPtrDealloc]
      by_cases hrk0 : (rkCap == 0#64) = true <;>
        simp only [hrk0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
      · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx25_2, hx26_2, hx27_2, hx28_2, htr2, hvregs_2⟩
      refine Drop.seq_clean (mid := (blkPl_338).base + 164#64)
        (P_mid := (fiveVec128HeadersAt stA g ∗
          vecCapPtrDealloc A hdrCap hdrPtr ∗ vecCapPtrDealloc A esCap esPtr ∗
          vecCapPtrDealloc A ct1Cap ct1Ptr) ∗
          A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ errBranchFrame A outA ekA res s0 st.epoch)
        (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
      · dsimp only [fiveVec128HeadersAt, g, vecCapPtrDealloc]
        by_cases hmk0 : (mkCap == 0#64) = true <;>
          simp only [hmk0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
        · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx20_3, hx25_3, hx26_3, hx27_3, hx28_3, htr3, hvregs_3⟩
        refine Drop.seq_clean (mid := (blkPl_338).base + 184#64)
          (P_mid := (fiveVec128HeadersAt stA g ∗
            vecCapPtrDealloc A esCap esPtr ∗ vecCapPtrDealloc A ct1Cap ct1Ptr) ∗
            A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ errBranchFrame A outA ekA res s0 st.epoch)
          (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
        · dsimp only [fiveVec128HeadersAt, g, vecCapPtrDealloc]
          by_cases hhdr0 : (hdrCap == 0#64) = true <;>
            simp only [hhdr0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
          · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp3]; ac_rfl) ?_; wp_done
        · intro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx20_4, hx25_4, hx26_4, hx27_4, hx28_4, htr4, hvregs_4⟩
          refine Drop.seq_clean (mid := (blkPl_338).base + 204#64)
            (P_mid := (fiveVec128HeadersAt stA g ∗ vecCapPtrDealloc A ct1Cap ct1Ptr) ∗
              A.pool ∗ stackAt (s0.sp - 208#64) allocHookStack ∗ errBranchFrame A outA ekA res s0 st.epoch)
            (Q := fun sm => ErrBranchPreserved s0 sm stA hdrPtr) ?_ ?_
          · dsimp only [fiveVec128HeadersAt, g, vecCapPtrDealloc]
            by_cases hes0 : (esCap == 0#64) = true <;>
              simp only [hes0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_steps; refine Drop.align_pre (by ac_rfl) ?_; wp_done
            · wp_steps; wp_apply; refine Drop.align_pre (by rw [hsp4]; ac_rfl) ?_; wp_done
          · intro s5 hpc5 hrun5 ⟨hsp5, hx19_5, hx20_5, hx25_5, hx26_5, hx27_5, hx28_5, htr5, hvregs_5⟩
            wp_conv_pre => unfold errBranchFrame
            refine SepWP.fold (Entails.of_eq (stackAt_sub208_extHook_split s0.sp).symm)
              (by sep_focus) ?_
            dsimp only [fiveVec128HeadersAt, g, vecCapPtrDealloc]
            by_cases hct1_0 : (ct1Cap == 0#64) = true <;>
              simp only [hct1_0, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · wp_step; wp_step
              refine SepWP.fold (fiveVec128HeadersAt_entails_memRegion_128 stA g)
                (by dsimp only [fiveVec128HeadersAt, g]; sep_focus) ?_
              exact h_epilogue outA stA ekA res st.epoch hsp0_align
                (by wp_norm_goal)
                (by wp_norm_lhs)
                (by simp only [State.sp, arm64_norm, hsp5])
                (by simp only [Reg.x25, arm64_norm, hx25_5]) (by simp only [Reg.x26, arm64_norm, hx26_5])
                (by simp only [Reg.x27, arm64_norm, hx27_5]) (by simp only [Reg.x28, arm64_norm, hx28_5])
                (by simp only [arm64_norm, htr5]) (by simp only [arm64_norm, hvregs_5]) (by ac_rfl)
            · have hct1_ne : ct1Cap ≠ 0#64 := ne_of_beq_false (Bool.eq_false_iff.mpr hct1_0)
              wp_step; wp_step; wp_step; wp_step
              refine SepWP.fold (fiveVec128HeadersAt_entails_memRegion_128 stA g)
                (by dsimp only [fiveVec128HeadersAt, g]; sep_focus) ?_
              exact h_tail outA stA ekA ct1Cap ct1Ptr res st.epoch
                hct1_ne hct1_lt hsp0_align
                (by wp_norm_goal)
                (by wp_norm_lhs)
                (by simp only [State.sp, arm64_norm, hsp5])
                (by simp only [Reg.x0, arm64_norm]) (by simp only [Reg.x1, arm64_norm])
                (by simp only [Reg.x25, arm64_norm, hx25_5]) (by simp only [Reg.x26, arm64_norm, hx26_5])
                (by simp only [Reg.x27, arm64_norm, hx27_5]) (by simp only [Reg.x28, arm64_norm, hx28_5])
                (by simp only [arm64_norm, htr5]) (by simp only [arm64_norm, hvregs_5]) (by ac_rfl)

/-- Closed `[LibsignalPlacement]` contract for `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek`
    (Block `338`, 99 instructions) from `HookSat` hypotheses. -/
theorem unchunked_ct1_sent_recv_ek_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (mlkemValidatePkSpec K)) :
    UnchunkedCt1SentRecvEkPlacedOkX A F K ext := by
  unfold UnchunkedCt1SentRecvEkPlacedOkX
  have hdealloc_call : subroutine_ok (lsProg_338 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") hdealloc
  have hval_call : subroutine_ok (lsProg_338 (Rust.withPanics ext))
      (lsρ "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes") (mlkemValidatePkSpec K) :=
    spqr_hook_ok_of_mem (sym := "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes") hval_pk
  simp only [unchunkedCt1SentRecvEkSpec, lsProg_338] at hdealloc_call hval_call ⊢
  have h_ok := unchunked_recv_ek_ok_branch_placed (F := F) hdealloc_call
  have h_err := unchunked_recv_ek_err_branch_placed (F := F) hdealloc_call
  wp_init x s0
  apply sepWP_post_bridge
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = x.outA := by assumption
  have hx1 : s0.readReg64 (Reg.gpr 1#5) = x.stA := by assumption
  have hx2 : s0.readReg64 (Reg.gpr 2#5) = x.st.epoch := by assumption
  have hx3 : s0.readReg64 (Reg.gpr 3#5) = x.ekA := by assumption
  have hrecv : x.st.recv_ek K x.st.epoch x.ek = StatesResult.ofError x.res := by assumption
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by assumption
  have hfsp_align : ((s0.sp - 208#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 208#64 hsp0_align (by decide)
  obtain ⟨hok_res, herr_res⟩ := unchunked_recv_ek_elim hrecv
  wp_conv_pre =>
    unfold unchunkedCt1SentAt
    rw [stackAt_unchunkedRecvEk_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.fold (vecU8_unfold_body_48 A x.stA x.st.hdr) (by sep_focus) ?_
  wp_pull_exists; rename_i hdrCap hdrPtr
  wp_focus_pure; rintro ⟨hhdr_le, hhdr_lt, _⟩
  refine SepWP.fold (vecU8_entails_slice_and_tail A x.ekA x.ek) (by sep_focus) ?_
  wp_pull_exists; rename_i ekCap ekPtr
  wp_focus_pure; rintro ⟨hek_le, hek_lt, hek_ne⟩
  wp_steps
  refine SepWP.fold (fold_unchunkedRecvEkSavedCells s0) (by sep_focus) ?_
  refine call_validatePk hval_call hdrPtr ekPtr x.st.hdr x.ek
    (ret_pc := (blkPl_338).base + 76#64) (sp_call := s0.sp - 208#64)
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [State.sp, arm64_norm]) hfsp_align
    (by simp only [Reg.lr, arm64_norm]) rfl
    (by simp only [Reg.x0, arm64_norm])
    (by simp only [Reg.x1, arm64_norm, BitVec.toNat_ofNat]; omega)
    (by simp only [Reg.x2, arm64_norm])
    (by simp only [Reg.x3, arm64_norm, BitVec.toNat_ofNat]; omega)
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 htr1 hvalid => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm, hx0, hx1, hx2, hx3] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
  by_cases hpk : K.validPkBytes x.st.hdr x.ek = true
  · have hbics : (BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = true :=
      (bics_255_eq_zero_iff (sf1.readReg64 (Reg.gpr 0#5))).mpr (hvalid.mpr hpk)
    wp_step; wp_step; wp_step
    refine h_ok x.outA x.stA x.ekA hdrCap hdrPtr ekCap ekPtr
      x.st x.ek x.res (hok_res hpk) hhdr_le hhdr_lt hek_le hek_lt hek_ne hsp0_align
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · wp_norm_goal
    · wp_norm_lhs
    · simp only [State.sp, arm64_norm, hsp1]
    · simp only [Reg.x19, arm64_norm, hx19_1]
    · simp only [Reg.x20, arm64_norm, hx20_1]
    · simp only [Reg.x21, arm64_norm, hx21_1]
    · simp only [Reg.x22, arm64_norm, hx22_1]
    · simp only [Reg.x23, arm64_norm, hx23_1]
    · simp only [Reg.x25, arm64_norm, hx25_1]
    · simp only [Reg.x26, arm64_norm, hx26_1]
    · simp only [Reg.x27, arm64_norm, hx27_1]
    · simp only [Reg.x28, arm64_norm, hx28_1]
    · simp only [arm64_norm, htr1]
    · simp only [arm64_norm, hvregs_1]
    · ac_rfl
  · have hpk_f : K.validPkBytes x.st.hdr x.ek = false := Bool.eq_false_iff.mpr hpk
    have hbics_not : ¬((BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = true) :=
      fun hb => hpk (hvalid.mp ((bics_255_eq_zero_iff (sf1.readReg64 (Reg.gpr 0#5))).mp hb))
    have hbics : (BitVec.truncate 32 (255#64 &&& ~~~BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) == 0#32) = false :=
      Bool.eq_false_iff.mpr hbics_not
    wp_step; wp_step; wp_step
    refine h_err x.outA x.stA x.ekA hdrCap hdrPtr ekCap ekPtr
      x.st x.ek x.res (herr_res hpk_f) hhdr_le hhdr_lt hek_le hek_lt hsp0_align
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · wp_norm_goal
    · wp_norm_lhs
    · simp only [State.sp, arm64_norm, hsp1]
    · simp only [Reg.x19, arm64_norm, hx19_1]
    · simp only [Reg.x20, arm64_norm, hx20_1]
    · simp only [Reg.x21, arm64_norm, hx21_1]
    · simp only [Reg.x23, arm64_norm, hx23_1]
    · simp only [Reg.x24, arm64_norm, hx24_1]
    · simp only [Reg.x25, arm64_norm, hx25_1]
    · simp only [Reg.x26, arm64_norm, hx26_1]
    · simp only [Reg.x27, arm64_norm, hx27_1]
    · simp only [Reg.x28, arm64_norm, hx28_1]
    · simp only [arm64_norm, htr1]
    · simp only [arm64_norm, hvregs_1]
    · ac_rfl

/-- `withLsCodeLoaded`-wrapped `[LibsignalPlacement]` contract for
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::recv_ek` (Block `338`), suitable for cross-block
    transfer via `ls_subroutine_ok_of_block`. -/
theorem unchunked_ct1_sent_recv_ek_placed_cl_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc" (rustDeallocSpec A))
    (hval_pk : HookSat (Rust.withPanics ext) "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem8mlkem76811incremental17validate_pk_bytes" (mlkemValidatePkSpec K)) :
    subroutine_ok (lsProg_338 (Rust.withPanics ext)) (blkPl_338).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)) :=
  subroutine_ok_withLsCodeLoaded_of_plain
    (unchunked_ct1_sent_recv_ek_placed_ok_x hdealloc hval_pk)

end CryptoVerification.SpqrV1.States.Leaves
