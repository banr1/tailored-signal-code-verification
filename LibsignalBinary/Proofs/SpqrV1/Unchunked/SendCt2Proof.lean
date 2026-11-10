/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Epilogue and Top-Level Proof

**Checked by Lean.**

Proves Segment 5b (`+836 → +964`) and the top-level fixed-base and `[LibsignalPlacement]`
contracts for `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L29a

open Lean Elab Tactic
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

elab "l29a_send_ct2_fetches_range " b:term:max H:term:max k0:num len:num : tactic => do
  let e ← ProofLib.CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"
  let offLit := Syntax.mkNumLit (toString e.val)
  evalTactic (← `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode
      CryptoVerification.SpqrV1.Unchunked.unchunkedSendCt2Bin $b $H
      unchunkedCt1SentEkReceivedSendCt2_fnOff $offLit:num $k0 $len))

end CryptoVerification.SpqrV1.Layout.L29a

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.LibsignalTripleRatchet.Keys
open NextKeyInternalFacts
open AgreeStateSimp
open DoReserveNorm
open CryptoVerification.SpqrV1.Layout.L29a

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  unchunkedCt1SentEkReceivedSendCt2_fnOff
  sliceConcat_fnOff doReserve7_fnOff mlkemEncaps2_fnOff
  MacHdrFacts.libcruxHmac_fnOff dealloc_fnOff
  (ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")
  (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_stub% "libcrux_hmac::hmac")
  (ls_hook% "libcrux_hmac::hmac")

/-! ## Segment 5b (`+836 → +964`): Output Stores, Deallocations, and Epilogue -/

theorem memRegion_104_cells (a : BitVec 64) :
    memRegion a 104 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗
        ((a + 96#64) ↦₆₄ v12)) := by
  rw [ProofLib.memRegion_cells a 13 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem vecU8_sp_272_entails (A : RustAlloc) (sp : BitVec 64) (bs : Bytes) :
    vecU8 A (sp - 272#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp - 272#64) ↦₆₄ cap) ∗ ((sp - 264#64) ↦₆₄ ptr) ∗
        ((sp - 256#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8HeapAt A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 272#64) cap ptr bs]
  have h1 : (sp - 272#64) + 8#64 = sp - 264#64 := by bv_omega
  have h2 : (sp - 272#64) + 16#64 = sp - 256#64 := by bv_omega
  rw [h1, h2]
  exact Entails.of_eq (by ac_rfl)

theorem slice_and_tail_entails_vecU8HeapAt (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) (hptr_ne : ptr ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ⊢ vecU8HeapAt A cap ptr bs := by
  unfold vecU8Tail vecU8HeapAt
  refine Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ ?_
  by_cases hc : cap = 0#64
  · subst hc
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
    subst hbs0
    simp only [beq_self_eq_true, ↓reduceIte, pointsToBytes_nil, sepConj_emp]
    exact Entails.refl _
  · have hcb : (cap == 0#64) = false := beq_false_of_ne hc
    have hc0 : cap ≠ 0 := hc
    simp only [hcb, hc0, Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem slice_and_tail_entails_live_memRegion (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes)
    (hle : bs.length ≤ cap.toNat) (hcap_lt : cap.toNat < 2 ^ 63) (hcap_ne : cap ≠ 0#64) :
    (ptr ↦ₛ bs) ∗ vecU8Tail A cap ptr bs ⊢ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  refine Entails.trans (slice_and_tail_entails_vecCapPtrDealloc A cap ptr bs hle hcap_lt) ?_
  unfold vecCapPtrDealloc
  have hcb : (cap == 0#64) = false := beq_false_of_ne hcap_ne
  simp only [hcb, Bool.false_eq_true, ↓reduceIte]
  exact Entails.refl _

theorem fold_stA_128 (stA v0 v1 v2 v3 v4 v5 : BitVec 64) :
    (stA ↦₆₄ v0) ∗ ((stA + 8#64) ↦₆₄ v1) ∗
      ((stA + 16#64) ↦₆₄ v2) ∗ ((stA + 24#64) ↦₆₄ v3) ∗
      ((stA + 32#64) ↦₆₄ v4) ∗ ((stA + 40#64) ↦₆₄ v5) ∗
      memRegion (stA + 48#64) 80 ⊢
      memRegion stA 128 := by
  rw [ProofLib.memRegion_split' (b := stA) (n := 48) (k := 80)
        (b' := stA + 48#64) rfl (by bv_omega) (by decide)]
  have h48 :
      (stA ↦₆₄ v0) ∗ ((stA + 8#64) ↦₆₄ v1) ∗
        ((stA + 16#64) ↦₆₄ v2) ∗ ((stA + 24#64) ↦₆₄ v3) ∗
        ((stA + 32#64) ↦₆₄ v4) ∗ ((stA + 40#64) ↦₆₄ v5) ⊢
        memRegion stA (8 * 6) := by
    rw [ProofLib.memRegion_cells stA 6 (by decide)]
    dsimp only [cells]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      emp_sepConj, sepConj_emp]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
      (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
        (Entails.of_eq (by ac_rfl)))))))
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_left h48)

theorem fold_vecU8_from_heap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : Bytes) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8HeapAt A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A a cap ptr bs]
  exact Entails.of_eq (by ac_rfl)

theorem fold_vecU8_ct2_56 (A : RustAlloc) (outA ptr_ct2 : BitVec 64) (ct2 : Bytes)
    (hct2_len : ct2.length = 128) (hptr_ne : ptr_ct2 ≠ 0#64) :
    ((outA + 56#64) ↦₆₄ 128#64) ∗ ((outA + 64#64) ↦₆₄ ptr_ct2) ∗
      ((outA + 72#64) ↦₆₄ 128#64) ∗ (ptr_ct2 ↦ₛ ct2) ∗ A.live ptr_ct2 128 1 ⊢
      vecU8 A (outA + 56#64) ct2 := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 128#64 (Entails.sepExists_right ptr_ct2 ?_)
  have h1 : (outA + 56#64) + 8#64 = outA + 64#64 := by bv_omega
  have h2 : (outA + 56#64) + 16#64 = outA + 72#64 := by bv_omega
  have hne128 : (128#64 : BitVec 64) ≠ 0 := by decide
  have htoNat128 : (128#64 : BitVec 64).toNat = 128 := rfl
  simp only [h1, h2, hct2_len, BitVec.ofNat_eq_ofNat, hne128, ↓reduceIte, htoNat128,
    Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp]
  rw [sepConj_left_comm ((outA + 56#64) ↦₆₄ 128#64 ∗ (outA + 64#64) ↦₆₄ ptr_ct2 ∗ (outA + 72#64) ↦₆₄ 128#64)]
  refine Entails.pure_right ⟨by decide, by decide, hptr_ne⟩ ?_
  exact Entails.of_eq (by ac_rfl)

theorem fold_outA_104 (A : RustAlloc) {F : ShaCompress}
    (x : UnchunkedSendCt2Ghost F)
    (rkCap rkPtr mkCap mkPtr ptr_ct2 macCap macPtr : BitVec 64)
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128) (hptr_ct2_ne : ptr_ct2 ≠ 0#64) :
    (x.outA ↦₆₄ rkCap) ∗ ((x.outA + 8#64) ↦₆₄ rkPtr) ∗
      ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
      vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
      ((x.outA + 24#64) ↦₆₄ mkCap) ∗ ((x.outA + 32#64) ↦₆₄ mkPtr) ∗
      ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
      vecU8HeapAt A mkCap mkPtr x.st.auth.macKey ∗
      ((x.outA + 48#64) ↦₆₄ x.st.epoch) ∗
      ((x.outA + 56#64) ↦₆₄ 128#64) ∗ ((x.outA + 64#64) ↦₆₄ ptr_ct2) ∗
      ((x.outA + 72#64) ↦₆₄ 128#64) ∗ (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
      ((x.outA + 80#64) ↦₆₄ macCap) ∗ ((x.outA + 88#64) ↦₆₄ macPtr) ∗
      ((x.outA + 96#64) ↦₆₄ BitVec.ofNat 64 x.mac.length) ∗
      vecU8HeapAt A macCap macPtr x.mac ⊢
      unchunkedCt2SentAt A x.outA x.outUc ∗
      vecU8 A (x.outA + 56#64) x.ct2 ∗
      vecU8 A (x.outA + 80#64) x.mac := by
  rw [houtUc]
  unfold unchunkedCt2SentAt authenticatorAt
  dsimp only []
  have hrk := fold_vecU8_from_heap A x.outA rkCap rkPtr x.st.auth.rootKey
  have hmk :
      ((x.outA + 24#64) ↦₆₄ mkCap) ∗ ((x.outA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        vecU8HeapAt A mkCap mkPtr x.st.auth.macKey ⊢
        vecU8 A (x.outA + 24#64) x.st.auth.macKey := by
    have h1 : (x.outA + 24#64) + 8#64 = x.outA + 32#64 := by bv_omega
    have h2 : (x.outA + 24#64) + 16#64 = x.outA + 40#64 := by bv_omega
    simpa only [h1, h2] using fold_vecU8_from_heap A (x.outA + 24#64) mkCap mkPtr x.st.auth.macKey
  have hct2 := fold_vecU8_ct2_56 A x.outA ptr_ct2 x.ct2 hct2_len hptr_ct2_ne
  have hmac :
      ((x.outA + 80#64) ↦₆₄ macCap) ∗ ((x.outA + 88#64) ↦₆₄ macPtr) ∗
        ((x.outA + 96#64) ↦₆₄ BitVec.ofNat 64 x.mac.length) ∗
        vecU8HeapAt A macCap macPtr x.mac ⊢
        vecU8 A (x.outA + 80#64) x.mac := by
    have h1 : (x.outA + 80#64) + 8#64 = x.outA + 88#64 := by bv_omega
    have h2 : (x.outA + 80#64) + 16#64 = x.outA + 96#64 := by bv_omega
    simpa only [h1, h2] using fold_vecU8_from_heap A (x.outA + 80#64) macCap macPtr x.mac
  refine Entails.trans (Entails.of_eq (show _ =
    ((x.outA ↦₆₄ rkCap) ∗ ((x.outA + 8#64) ↦₆₄ rkPtr) ∗
      ((x.outA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
      vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey) ∗
    (((x.outA + 24#64) ↦₆₄ mkCap) ∗ ((x.outA + 32#64) ↦₆₄ mkPtr) ∗
      ((x.outA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
      vecU8HeapAt A mkCap mkPtr x.st.auth.macKey) ∗
    ((x.outA + 48#64) ↦₆₄ x.st.epoch) ∗
    (((x.outA + 56#64) ↦₆₄ 128#64) ∗ ((x.outA + 64#64) ↦₆₄ ptr_ct2) ∗
      ((x.outA + 72#64) ↦₆₄ 128#64) ∗ (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1) ∗
    (((x.outA + 80#64) ↦₆₄ macCap) ∗ ((x.outA + 88#64) ↦₆₄ macPtr) ∗
      ((x.outA + 96#64) ↦₆₄ BitVec.ofNat 64 x.mac.length) ∗
      vecU8HeapAt A macCap macPtr x.mac) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono hrk (sepConj_mono hmk (sepConj_mono (Entails.refl _) (sepConj_mono hct2 hmac)))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem fold_sp_264_120 (sp v1 v2 : BitVec 64) :
    ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
      memRegion (sp - 248#64) 24 ∗ memRegion (sp - 224#64) 80 ⊢
      memRegion (sp - 264#64) 120 := by
  rw [ProofLib.memRegion_split' (b := sp - 264#64) (n := 8) (k := 112)
        (b' := sp - 256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 256#64) (n := 8) (k := 104)
        (b' := sp - 248#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 248#64) (n := 24) (k := 80)
        (b' := sp - 224#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Drop.pointsTo64_entails_memRegion (sp - 264#64) v1)
    (sepConj_mono_left (Drop.pointsTo64_entails_memRegion (sp - 256#64) v2))

theorem fold_stackAt_unchunkedSendCt2 (s0 : State)
    (l0 l1 l2 l3 l4 l5 s64 epoch : BitVec 64) :
    stackAt (s0.sp - 336#64) extHookStack ∗
      memRegion (s0.sp - 336#64) 8 ∗
      ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
      ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
      ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
      memRegion (s0.sp - 280#64) 8 ∗
      ((s0.sp - 272#64) ↦₆₄ s64) ∗
      memRegion (s0.sp - 264#64) 120 ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 120#64) ↦ₛ toBEBytes 8 epoch) ∗
      memRegion (s0.sp - 112#64) 16 ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
      ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
      ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
      ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      stackAt s0.sp unchunkedSendCt2Stack := by
  rw [← pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) epoch,
      stackAt_unchunkedSendCt2_split s0.sp]
  have h_l :
      ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ⊢
      ∃∗ l0 : BitVec 64, ∃∗ l1 : BitVec 64, ∃∗ l2 : BitVec 64,
       ∃∗ l3 : BitVec 64, ∃∗ l4 : BitVec 64, ∃∗ l5 : BitVec 64,
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) :=
    Entails.sepExists_right l0 (Entails.sepExists_right l1 (Entails.sepExists_right l2
      (Entails.sepExists_right l3 (Entails.sepExists_right l4 (Entails.sepExists_right l5
        (Entails.refl _))))))
  have h_s64 : ((s0.sp - 272#64) ↦₆₄ s64) ⊢ ∃∗ s64 : BitVec 64, (s0.sp - 272#64) ↦₆₄ s64 :=
    Entails.sepExists_right s64 (Entails.refl _)
  have h_e0 : ((s0.sp - 120#64) ↦₆₄ rev64 epoch) ⊢ ∃∗ e0 : BitVec 64, (s0.sp - 120#64) ↦₆₄ e0 :=
    Entails.sepExists_right (rev64 epoch) (Entails.refl _)
  have h_c :
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19) ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
       ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
       ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) :=
    Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
      (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
        (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
          (Entails.sepExists_right _ (Entails.sepExists_right _ (Entails.sepExists_right _
            (Entails.refl _))))))))))))
  refine Entails.trans (Entails.of_eq (show _ =
    stackAt (s0.sp - 336#64) extHookStack ∗
      memRegion (s0.sp - 336#64) 8 ∗
      (((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5)) ∗
      memRegion (s0.sp - 280#64) 8 ∗
      ((s0.sp - 272#64) ↦₆₄ s64) ∗
      memRegion (s0.sp - 264#64) 120 ∗
      memRegion (s0.sp - 144#64) 24 ∗
      ((s0.sp - 120#64) ↦₆₄ rev64 epoch) ∗
      memRegion (s0.sp - 112#64) 16 ∗
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
        ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
        ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
        ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
        ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) by ac_rfl)) ?_
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono h_l
        (sepConj_mono (Entails.refl _)
          (sepConj_mono h_s64
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (Entails.refl _)
                (sepConj_mono h_e0
                  (sepConj_mono (Entails.refl _) h_c))))))))

set_option maxHeartbeats 1600000 in
/-- Segment 5b (`+836 → +964`): store `(Ct2Sent, ct2, mac)` into `outA`, deallocate
`ct1`, `es`, and `ek`, restore callee-saved registers, and return. -/
theorem send_ct2_epilogue_ret_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (x : UnchunkedSendCt2Ghost F)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2RoAt b ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PostQ A F K b x s0 R)
      (sendCt2PostQp A F K b x s0 R) := by
  have h_dealloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_rel% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) :=
    dealloc_ok_at_sendCt2 hA
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hcap_ct1'_ne : cap_ct1' ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
  have hcap_ct1'_beq : (cap_ct1' == 0#64) = false := beq_false_of_ne hcap_ct1'_ne
  have hesCap_ne : esCap ≠ 0#64 := by
    intro h0; subst h0; simp [hes_len] at hes_le
  have hesCap_beq : (esCap == 0#64) = false := beq_false_of_ne hesCap_ne
  have hekCap_ne : ekCap ≠ 0#64 := by
    intro h0; subst h0; simp [hek_len] at hek_le
  have hekCap_beq : (ekCap == 0#64) = false := beq_false_of_ne hekCap_ne
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27
  unfold tripleRatchetProgAtExt at hpc h_dealloc ⊢
  l29a_send_ct2_fetches_range b (Rust.withPanics ext) 836 132
  clear hA
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name = entry
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.fold
    (slice_and_tail_entails_vecU8HeapAt A mkCap mkPtr x.st.auth.macKey hmk_le hmk_max hmk_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A esCap esPtr x.st.es hes_le hes_max hesCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A ekCap ekPtr x.st.ek hek_le hek_max hekCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold (vecU8_sp_272_entails A s0.sp x.mac) (by sep_focus) ?_
  sep_elim_exists
  rename_i macCap macPtr
  refine SepWPp.rw_pre (by rw [memRegion_104_cells x.outA]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_mid (mid := entry + 936#64) ?_
  wp_steps
  refine SepWP.fold
    (fold_stA_128 x.stA rkCap rkPtr (BitVec.ofNat 64 x.st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 x.st.auth.macKey.length))
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_outA_104 A x rkCap rkPtr mkCap mkPtr ptr_ct2 macCap macPtr
      houtUc hct2_len hptr_ct2_ne)
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_sp_264_120 s0.sp macPtr (BitVec.ofNat 64 x.mac.length))
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp))
    (by sep_focus) ?_
  refine call_rustDealloc h_dealloc ptr_ct1' cap_ct1'.toNat 1
    (s0 := s0) (ret_pc := entry + 896#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1
  wp_steps
  refine call_rustDealloc h_dealloc esPtr esCap.toNat 1
    (s0 := s0) (ret_pc := entry + 916#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_)
  rcases hcs2 with ⟨_, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  simp only [arm64_norm] at hx20_2
  wp_steps
  refine call_rustDealloc h_dealloc ekPtr ekCap.toNat 1
    (s0 := s0) (ret_pc := entry + 936#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
  rcases hcs3 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  refine SepWP.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.rw_pre (by unfold sendCt2CalleeSavedAt; rfl) ?_
  have hsp3_norm : sf3.readReg64 .sp = s0.sp - 336#64 := hsp3
  simp only [wp_norm, arm64_norm] at hsp3_norm
  refine SepWPp.of_sepWP_mid (mid := s0.readReg64 .x30) ?_
  wp_steps
  refine SepWP.fold
    (fold_stackAt_unchunkedSendCt2 s0 esCap ekCap x.st.epoch
      cap_ct1' ptr_ct1' (BitVec.ofNat 64 x.st.ct1.length) macCap x.st.epoch)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨fun hm => ?_, by simp only [State.sp, wp_norm, arm64_norm, *], ?_⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by simp only [wp_norm, arm64_norm, *], ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, Reg.x29, wp_norm, arm64_norm, *]

/-! ## Top-Level Fixed-Base Theorems -/

private theorem hookSat_shimWithStack_of_noAllocShim {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName noAllocShimSpec) (stk : Nat) :
    HookSat ext shimName (session2ShimSpecWithStack stk) := by
  obtain ⟨f, hf, hok⟩ := hshim
  refine ⟨f, hf, ?_⟩
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ noAllocShimSpec.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [noAllocShimSpec, session2ShimSpecWithStack] at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  obtain ⟨hkf, hsym, hout⟩ := hok x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec, session2ShimSpecWithStack] at hq ⊢
    simpa only [sepConj_assoc] using hq
  · rw [show noAllocShimSpec.onPanic x s0 (f s0) = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hp2
    exact False.elim hp2.1
  · rw [show noAllocShimSpec.onExit x c s0 (f s0) = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at he2
    exact False.elim he2.1
  · rw [show noAllocShimSpec.onOom x s0 (f s0) = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at ho2
    exact False.elim ho2.1

set_option maxHeartbeats 1200000 in
/-- `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (281 instructions)
satisfies `unchunkedCt1SentEkReceivedSendCt2Spec A F K b` on `tripleRatchetProgAtExt b ext`
under `AllocContracts4K b A ext` and `sliceConcat3Spec A`. -/
theorem unchunked_ct1_sent_ek_received_send_ct2_ok_4k {b : BitVec 64}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec A))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  refine ⟨(unchunkedCt1SentEkReceivedSendCt2Spec A F K b).pre x s0, R, hpre, ?_⟩
  change SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
    ((unchunkedCt1SentEkReceivedSendCt2Spec A F K b).pre x s0)
    (sendCt2PostQ A F K b x s0 R)
    (sendCt2PostQp A F K b x s0 R)
  dsimp only [unchunkedCt1SentEkReceivedSendCt2Spec]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hb, hx0, hx1, hmodel⟩
  obtain ⟨henc_ok, hmac_ok, houtUc⟩ := send_ct2_ok_elim hmodel
  obtain ⟨hes_len, hek_len, esVec, ekVec, hesVec, hekVec, hct2_eq⟩ := encaps2_ok_elim henc_ok
  obtain ⟨hmk_lt32, hdata_lt32, hmac_eq⟩ := macCt_ok_elim hmac_ok
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hct1_lt32 : x.st.ct1.length < 2 ^ 32 := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hdata_lt32
    omega
  unfold unchunkedCt1SentEkReceivedAt authenticatorAt
  refine SepWPp.fold (vecU8_entails_cells_and_heap A x.stA x.st.auth.rootKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i rkCap rkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hrk_le, hrk_max, hrk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 24#64) x.st.auth.macKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i mkCap mkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 48#64) x.st.es) (by sep_focus) ?_
  sep_elim_exists
  rename_i esCap esPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_max, hes_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 72#64) x.st.ek) (by sep_focus) ?_
  sep_elim_exists
  rename_i ekCap ekPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hek_le, hek_max, hek_ne⟩
  refine SepWPp.fold (vecU8_entails_cells_and_heap A (x.stA + 96#64) x.st.ct1) (by sep_focus) ?_
  sep_elim_exists
  rename_i ct1Cap ct1Ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_max, hct1_ne⟩
  refine SepWPp.rw_pre (by rw [stackAt_unchunkedSendCt2_split s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 e0 s64 l0 l1 l2 l3 l4 l5
  refine SepWPp.rw_pre ?_
    (SepWPp.of_sepWP_mid
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
      (SepWP.mono
        (send_ct2_prologue_to_scan A x.outA x.stA x.st
          rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
          l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0
          (memRegion x.outA 104 ∗
            vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
            (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
            (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A esCap esPtr x.st.es ∗
            (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
            unchunkedSendCt2RoAt b ∗ A.pool ∗
            stackAt (s0.sp - 336#64) extHookStack ∗
            memRegion (s0.sp - 336#64) 8 ∗
            memRegion (s0.sp - 280#64) 8 ∗
            memRegion (s0.sp - 144#64) 24 ∗
            memRegion (s0.sp - 112#64) 16)
          hes_len hek_len hpc hrun hsp hx0 hx1)
        ?_))
  · ac_rfl
  rintro st1 _ hpc1 hrun1 ⟨rfl, hsp1, htr1, hvregs_1, hx8_1, hx9_1, hx10_1, hx11_1, hx13_1,
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  let F_base : SepProp :=
    memRegion x.outA 104 ∗
    (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
    ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
    ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
    ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
    memRegion (x.stA + 48#64) 80 ∗
    vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
    vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
    ((s0.sp - 328#64) ↦₆₄ esCap) ∗ vecU8Tail A esCap esPtr x.st.es ∗
    ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
    memRegion (s0.sp - 336#64) 8 ∗
    memRegion (s0.sp - 280#64) 8 ∗
    memRegion (s0.sp - 112#64) 16 ∗
    sendCt2CalleeSavedAt s0
  refine SepWPp.rw_pre ?_
    (send_ct2_scan_to_628_wpp hA x esPtr s0 st1
      (F_base ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
      hb hes_len hpc1 hrun1 hsp1 hsp htr1 hvregs_1
      hx8_1 hx9_1 hx10_1 hx11_1 hx13_1 hx19_1 hx28_1
      (fun st2 esWorkPtr hpc2 hrun2 hsp2 htr2 hvregs_2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  · unfold unchunkedSendCt2RoAt F_base; ac_rfl
  rw [hx20_1] at hx20_2
  rw [hx23_1] at hx23_2
  rw [hx24_1] at hx24_2
  rw [hx25_1] at hx25_2
  rw [hx26_1] at hx26_2
  rw [hx27_1] at hx27_2
  rw [hx29_1] at hx29_2
  refine SepWPp.rw_pre ?_
    (send_ct2_628_to_690_wpp hA hencaps2 x esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_base ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
      hesVec hekVec hct2_eq hek_ne hpc2 hrun2 hsp2 hsp htr2 hvregs_2
      hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2
      (fun st3 ptr_ct2 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs_3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  · ac_rfl
  rw [hx23_2] at hx23_3
  rw [hx24_2] at hx24_3
  rw [hx25_2] at hx25_3
  rw [hx26_2] at hx26_3
  rw [hx29_2] at hx29_3
  refine SepWPp.rw_pre ?_
    (send_ct2_reserve_ct1_wpp hA x ct1Cap ct1Ptr s0 st3
      (F_base ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel)) R
      hct1_lt32 hpc3 hrun3 hsp3 hsp htr3 hvregs_3
      (fun st4 cap_ct1' ptr_ct1' hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs_4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 => ?_))
  · ac_rfl
  rw [hx19_3] at hx19_4
  rw [hx20_3] at hx20_4
  rw [hx23_3] at hx23_4
  rw [hx24_3] at hx24_4
  rw [hx25_3] at hx25_4
  rw [hx26_3] at hx26_4
  rw [hx27_3] at hx27_4
  rw [hx29_3] at hx29_4
  refine SepWPp.rw_pre ?_
    (send_ct2_append_hmac_wpp hA hconcat3 hhmac x mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_base ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1) R
      hb hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp htr4 hvregs_4 hx1_4 hx25_4 hx26_4 hx27_4 hx29_4
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs_5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  · ac_rfl
  rw [hx19_4] at hx19_5
  rw [hx20_4] at hx20_5
  rw [hx23_4] at hx23_5
  rw [hx24_4] at hx24_5
  refine SepWPp.rw_pre (by unfold unchunkedSendCt2RoAt F_base; ac_rfl)
    (send_ct2_epilogue_ret_wpp hA x
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
      s0 st5 R
      houtUc hct2_len hes_len hek_len
      hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
      hpc5 hrun5 hsp5 hsp htr5 hvregs_5
      hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5)

theorem unchunked_ct1_sent_ek_received_send_ct2_ok_4k_of_hooks {b : BitVec 64}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack))
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) :=
  unchunked_ct1_sent_ek_received_send_ct2_ok_4k hA
    (slice_concat_3_spec_ok_ext_withStack
      (hookSat_shimWithStack_of_noAllocShim hshim allocHookStack) halloc hmc hRO)
    hencaps2 hhmac

theorem unchunked_ct1_sent_ek_received_send_ct2_ok_ext {b : BitVec 64}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A F K b) := by
  have hRO4K : HookSat ext memcpyName sessionMemcpyROSpec4K := by
    rcases hRO with ⟨fn, hfn, hok⟩
    exact ⟨fn, hfn, hok⟩
  have h0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyROSpec4K := by
    have h := hook_ok_at (P := CryptoVerification.libsignalSessionCode) (b := b) (hooks := ext)
      (name := memcpyName) (hname := memcpyName)
      (stub := CryptoVerification.libsignalSessionCode.fnOff memcpyName)
      (k := 0) rfl (Nat.add_zero _) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hRO4K
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  exact unchunked_ct1_sent_ek_received_send_ct2_ok_4k
    (AllocContracts4K.of_allocContracts hA fun stk _ _ =>
      subroutine_ok_withStack_of_subroutine_ok h0 stk)
    (slice_concat_3_spec_ok_ext hA hRO) hencaps2 hhmac

/-! ## Relocatable `[LibsignalPlacement]` Segment 5b and Top-Level Theorems -/

set_option maxHeartbeats 1600000 in
/-- Segment 5b (`+836 → +964`) under `[LibsignalPlacement]`: store `(Ct2Sent, ct2, mac)` into `outA`,
deallocate `ct1`, `es`, and `ek`, restore callee-saved registers, and return. -/
theorem send_ct2_epilogue_ret_placed_wpp [LibsignalPlacement] {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_dealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (x : UnchunkedSendCt2Ghost F)
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2 : BitVec 64)
    (s0 st : State) (R : SepProp)
    (houtUc : x.outUc = { epoch := x.st.epoch, auth := x.st.auth })
    (hct2_len : x.ct2.length = 128)
    (hes_len : x.st.es.length = 2080)
    (hek_len : x.st.ek.length = 1152)
    (hmk_le : x.st.auth.macKey.length ≤ mkCap.toNat)
    (hmk_max : mkCap.toNat < 2 ^ 63)
    (hmk_ne : mkPtr ≠ 0#64)
    (hes_le : x.st.es.length ≤ esCap.toNat)
    (hes_max : esCap.toNat < 2 ^ 63)
    (hek_le : x.st.ek.length ≤ ekCap.toNat)
    (hek_max : ekCap.toNat < 2 ^ 63)
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hptr_ct2_ne : ptr_ct2 ≠ 0#64)
    (hpc : st.pc = (blkPl_347).base + 836#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx22 : st.readReg64 .x22 = ptr_ct1')
    (hx23 : st.readReg64 .x23 = x.outA)
    (hx24 : st.readReg64 .x24 = x.stA)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2) :
    SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) st
      (memRegion x.outA 104 ∗
        (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
        ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
        ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
        ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
        memRegion (x.stA + 48#64) 80 ∗
        vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
        ((s0.sp - 328#64) ↦₆₄ esCap) ∗ (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A esCap esPtr x.st.es ∗
        ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        memRegion ptr_ct1' cap_ct1'.toNat ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        A.live ptr_ct2 128 1 ∗
        vecU8 A (s0.sp - 272#64) x.mac ∗
        memRegion (s0.sp - 336#64) 8 ∗
        memRegion (s0.sp - 280#64) 8 ∗
        memRegion (s0.sp - 248#64) 24 ∗
        memRegion (s0.sp - 224#64) 80 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
        memRegion (s0.sp - 112#64) 16 ∗
        sendCt2CalleeSavedAt s0 ∗
        unchunkedSendCt2PlacedRoAt ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack)
      (sendCt2PlacedPostQ A F K x s0 R)
      (sendCt2PlacedPostQp A F K x s0 R) := by
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hcap_ct1'_ne : cap_ct1' ≠ 0#64 := cap_ne_zero_of_add_128_le hge128
  have hcap_ct1'_beq : (cap_ct1' == 0#64) = false := beq_false_of_ne hcap_ct1'_ne
  have hesCap_ne : esCap ≠ 0#64 := by
    intro h0; subst h0; simp [hes_len] at hes_le
  have hesCap_beq : (esCap == 0#64) = false := beq_false_of_ne hesCap_ne
  have hekCap_ne : ekCap ≠ 0#64 := by
    intro h0; subst h0; simp [hek_len] at hek_le
  have hekCap_beq : (ekCap == 0#64) = false := beq_false_of_ne hekCap_ne
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx22 hx23 hx24 hx25 hx26 hx27
  refine SepWPp.fold
    (slice_and_tail_entails_vecU8HeapAt A mkCap mkPtr x.st.auth.macKey hmk_le hmk_max hmk_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A esCap esPtr x.st.es hes_le hes_max hesCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold
    (slice_and_tail_entails_live_memRegion A ekCap ekPtr x.st.ek hek_le hek_max hekCap_ne)
    (by sep_focus) ?_
  refine SepWPp.fold (vecU8_sp_272_entails A s0.sp x.mac) (by sep_focus) ?_
  sep_elim_exists
  rename_i macCap macPtr
  refine SepWPp.rw_pre (by rw [memRegion_104_cells x.outA]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_mid (mid := (blkPl_347).base + 936#64) ?_
  wp_steps
  refine SepWP.fold
    (fold_stA_128 x.stA rkCap rkPtr (BitVec.ofNat 64 x.st.auth.rootKey.length)
      mkCap mkPtr (BitVec.ofNat 64 x.st.auth.macKey.length))
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_outA_104 A x rkCap rkPtr mkCap mkPtr ptr_ct2 macCap macPtr
      houtUc hct2_len hptr_ct2_ne)
    (by sep_focus) ?_
  refine SepWP.fold
    (fold_sp_264_120 s0.sp macPtr (BitVec.ofNat 64 x.mac.length))
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp))
    (by sep_focus) ?_
  refine call_rustDealloc h_dealloc ptr_ct1' cap_ct1'.toNat 1
    (s0 := s0) (ret_pc := (blkPl_347).base + 896#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, _, _, _, _, _, _, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1
  wp_steps
  refine call_rustDealloc h_dealloc esPtr esCap.toNat 1
    (s0 := s0) (ret_pc := (blkPl_347).base + 916#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 htr2 hcs2 => ?_)
  rcases hcs2 with ⟨_, hx20_2, _, _, _, _, _, _, _, _, _, hvregs_2⟩
  simp only [arm64_norm] at hx20_2
  wp_steps
  refine call_rustDealloc h_dealloc ekPtr ekCap.toNat 1
    (s0 := s0) (ret_pc := (blkPl_347).base + 936#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
  rcases hcs3 with ⟨_, _, _, _, _, _, _, _, _, _, _, hvregs_3⟩
  refine SepWP.fold
    (Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.rw_pre (by unfold sendCt2CalleeSavedAt; rfl) ?_
  have hsp3_norm : sf3.readReg64 .sp = s0.sp - 336#64 := hsp3
  simp only [wp_norm, arm64_norm] at hsp3_norm
  refine SepWPp.of_sepWP_mid (mid := s0.readReg64 .x30) ?_
  wp_steps
  refine SepWP.fold
    (fold_stackAt_unchunkedSendCt2 s0 esCap ekCap x.st.epoch
      cap_ct1' ptr_ct1' (BitVec.ofNat 64 x.st.ct1.length) macCap x.st.epoch)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨fun hm => ?_, by simp only [State.sp, wp_norm, arm64_norm, *], ?_⟩
  · dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by simp only [wp_norm, arm64_norm, *], ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.fp, Reg.x29, wp_norm, arm64_norm, *]

set_option maxHeartbeats 1200000 in
theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec A))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec A))
    (hshim : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustNoAllocShimSym) noAllocShimSpec)
    (halloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrRustDeallocSym) (rustDeallocSpec A))
    (hmemcpy : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMemcpySym) framelessMemcpySpec)
    (henc : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrMlkemEncaps2Sym) (mlkemEncaps2Spec K))
    (hhmac : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsρ spqrLibcruxHmacSym) (libcruxHmacSpec F A))
    (hpan : ((blkPC_347).rebase (blkPl_347).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K) := by
  have hhmac_safe := libcrux_hmac_safe_of_subroutine_ok hhmac
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  refine ⟨(unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K).pre x s0, R, hpre, ?_⟩
  change SepWPp ((blkPC_347).rebase (blkPl_347).base H) (s0.readReg64 .x30) s0
    ((unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K).pre x s0)
    (sendCt2PlacedPostQ A F K x s0 R)
    (sendCt2PlacedPostQp A F K x s0 R)
  dsimp only [unchunkedCt1SentEkReceivedSendCt2PlacedSpec]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hx0, hx1, hmodel⟩
  obtain ⟨henc_ok, hmac_ok, houtUc⟩ := send_ct2_ok_elim hmodel
  obtain ⟨hes_len, hek_len, esVec, ekVec, hesVec, hekVec, hct2_eq⟩ := encaps2_ok_elim henc_ok
  obtain ⟨hmk_lt32, hdata_lt32, hmac_eq⟩ := macCt_ok_elim hmac_ok
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hct1_lt32 : x.st.ct1.length < 2 ^ 32 := by
    simp only [List.length_append, ctLabel_length, toBEBytes_8_length, hct2_len] at hdata_lt32
    omega
  unfold unchunkedCt1SentEkReceivedAt authenticatorAt
  refine SepWPp.fold (vecU8_entails_cells_and_heap A x.stA x.st.auth.rootKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i rkCap rkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hrk_le, hrk_max, hrk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 24#64) x.st.auth.macKey) (by sep_focus) ?_
  sep_elim_exists
  rename_i mkCap mkPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hmk_le, hmk_max, hmk_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 48#64) x.st.es) (by sep_focus) ?_
  sep_elim_exists
  rename_i esCap esPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hes_le, hes_max, hes_ne⟩
  refine SepWPp.fold (vecU8_entails_slice_and_tail A (x.stA + 72#64) x.st.ek) (by sep_focus) ?_
  sep_elim_exists
  rename_i ekCap ekPtr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hek_le, hek_max, hek_ne⟩
  refine SepWPp.fold (vecU8_entails_cells_and_heap A (x.stA + 96#64) x.st.ct1) (by sep_focus) ?_
  sep_elim_exists
  rename_i ct1Cap ct1Ptr
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hct1_le, hct1_max, hct1_ne⟩
  refine SepWPp.rw_pre (by rw [stackAt_unchunkedSendCt2_split s0.sp]) ?_
  sep_elim_exists
  rename_i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 e0 s64 l0 l1 l2 l3 l4 l5
  refine SepWPp.rw_pre ?_
    (SepWPp.of_sepWP_mid
      (mid := (blkPl_347).base + 0x88#64)
      (SepWP.mono
        (send_ct2_prologue_to_scan_placed A x.outA x.stA x.st
          rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
          l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 s0
          (memRegion x.outA 104 ∗
            vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
            (mkPtr ↦ₛ x.st.auth.macKey) ∗ vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
            (esPtr ↦ₛ x.st.es) ∗ vecU8Tail A esCap esPtr x.st.es ∗
            (ekPtr ↦ₛ x.st.ek) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
            unchunkedSendCt2PlacedRoAt ∗ A.pool ∗
            stackAt (s0.sp - 336#64) extHookStack ∗
            memRegion (s0.sp - 336#64) 8 ∗
            memRegion (s0.sp - 280#64) 8 ∗
            memRegion (s0.sp - 144#64) 24 ∗
            memRegion (s0.sp - 112#64) 16)
          hes_len hek_len hpc hrun hsp hx0 hx1)
        ?_))
  · ac_rfl
  rintro st1 _ hpc1 hrun1 ⟨rfl, hsp1, htr1, hvregs_1, hx8_1, hx9_1, hx10_1, hx11_1, hx13_1,
    hx19_1, hx20_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1⟩
  let F_base : SepProp :=
    memRegion x.outA 104 ∗
    (x.stA ↦₆₄ rkCap) ∗ ((x.stA + 8#64) ↦₆₄ rkPtr) ∗
    ((x.stA + 16#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.rootKey.length) ∗
    ((x.stA + 24#64) ↦₆₄ mkCap) ∗ ((x.stA + 32#64) ↦₆₄ mkPtr) ∗
    ((x.stA + 40#64) ↦₆₄ BitVec.ofNat 64 x.st.auth.macKey.length) ∗
    memRegion (x.stA + 48#64) 80 ∗
    vecU8HeapAt A rkCap rkPtr x.st.auth.rootKey ∗
    vecU8Tail A mkCap mkPtr x.st.auth.macKey ∗
    ((s0.sp - 328#64) ↦₆₄ esCap) ∗ vecU8Tail A esCap esPtr x.st.es ∗
    ((s0.sp - 320#64) ↦₆₄ ekCap) ∗ vecU8Tail A ekCap ekPtr x.st.ek ∗
    memRegion (s0.sp - 336#64) 8 ∗
    memRegion (s0.sp - 280#64) 8 ∗
    memRegion (s0.sp - 112#64) 16 ∗
    sendCt2CalleeSavedAt s0
  refine SepWPp.rw_pre ?_
    (send_ct2_scan_to_628_placed_wpp hshim halloc hmemcpy hpan x esPtr s0 st1
      (F_base ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
      hes_len hpc1 hrun1 hsp1 hsp htr1 hvregs_1
      hx8_1 hx9_1 hx10_1 hx11_1 hx13_1 hx19_1 hx28_1
      (fun st2 esWorkPtr hpc2 hrun2 hsp2 htr2 hvregs_2 hx19_2 hx20_2 hx21_2 hx22_2
        hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => ?_))
  · unfold unchunkedSendCt2PlacedRoAt F_base; ac_rfl
  rw [hx20_1] at hx20_2
  rw [hx23_1] at hx23_2
  rw [hx24_1] at hx24_2
  rw [hx25_1] at hx25_2
  rw [hx26_1] at hx26_2
  rw [hx27_1] at hx27_2
  rw [hx29_1] at hx29_2
  refine SepWPp.rw_pre ?_
    (send_ct2_628_to_690_placed_wpp henc hshim halloc hdealloc hpan x esPtr ekPtr esWorkPtr esVec ekVec s0 st2
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        vecU8At A (s0.sp - 304#64) ct1Cap ct1Ptr x.st.ct1 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
      hesVec hekVec hct2_eq hek_ne hpc2 hrun2 hsp2 hsp htr2 hvregs_2
      hx19_2 hx20_2 hx21_2 hx22_2 hx27_2 hx28_2
      (fun st3 ptr_ct2 hptr_ct2_ne hpc3 hrun3 hsp3 htr3 hvregs_3
        hx19_3 hx20_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 => ?_))
  · ac_rfl
  rw [hx23_2] at hx23_3
  rw [hx24_2] at hx24_3
  rw [hx25_2] at hx25_3
  rw [hx26_2] at hx26_3
  rw [hx29_2] at hx29_3
  refine SepWPp.rw_pre ?_
    (send_ct2_reserve_ct1_placed_wpp h_res x ct1Cap ct1Ptr s0 st3
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗ A.live ptr_ct2 128 1 ∗
        memRegion (s0.sp - 272#64) 128 ∗ (mkPtr ↦ₛ x.st.auth.macKey) ∗
        ((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((lsρ "spqr:.rodata..Lanon.137") ↦ᵣ Authenticator.ctLabel)) R
      hct1_lt32 hpc3 hrun3 hsp3 hsp htr3 hvregs_3
      (fun st4 cap_ct1' ptr_ct1' hcap_ct1'_ne hge128 hmax_ct1' hptr_ct1'_ne
        hpc4 hrun4 hsp4 htr4 hvregs_4 hx1_4 hx19_4 hx20_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx29_4 => ?_))
  · ac_rfl
  rw [hx19_3] at hx19_4
  rw [hx20_3] at hx20_4
  rw [hx23_3] at hx23_4
  rw [hx24_3] at hx24_4
  rw [hx25_3] at hx25_4
  rw [hx26_3] at hx26_4
  rw [hx27_3] at hx27_4
  rw [hx29_3] at hx29_4
  refine SepWPp.rw_pre ?_
    (send_ct2_append_hmac_placed_wpp h_concat3 hhmac_safe hdealloc x mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 s0 st4
      (F_base ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ (esPtr ↦ₛ x.st.es) ∗ (ekPtr ↦ₛ x.st.ek) ∗
        A.live ptr_ct2 128 1) R
      hct2_len hmk_lt32 hdata_lt32 hmac_eq hge128 hmax_ct1'
      hpc4 hrun4 hsp4 hsp htr4 hvregs_4 hx1_4 hx25_4 hx26_4 hx27_4 hx29_4
      (fun st5 hpc5 hrun5 hsp5 htr5 hvregs_5 hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx29_5 => ?_))
  · ac_rfl
  rw [hx19_4] at hx19_5
  rw [hx20_4] at hx20_5
  rw [hx23_4] at hx23_5
  rw [hx24_4] at hx24_5
  refine SepWPp.rw_pre (by unfold unchunkedSendCt2PlacedRoAt F_base; ac_rfl)
    (send_ct2_epilogue_ret_placed_wpp hdealloc x
      rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr cap_ct1' ptr_ct1' ptr_ct2
      s0 st5 R
      houtUc hct2_len hes_len hek_len
      hmk_le hmk_max hmk_ne hes_le hes_max hek_le hek_max hge128 hptr_ct2_ne
      hpc5 hrun5 hsp5 hsp htr5 hvregs_5
      hx19_5 hx20_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5)

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec A))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec A))
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K) :=
  unchunked_ct1_sent_ek_received_send_ct2_placed_ok_of_contracts h_res h_concat3
    (spqr_hook_ok_of_mem (sym := spqrRustNoAllocShimSym) hshim)
    (spqr_hook_ok_of_mem (sym := spqrRustAllocSym) halloc)
    (spqr_hook_ok_of_mem (sym := spqrRustDeallocSym) hdealloc)
    (spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy)
    (spqr_hook_ok_of_mem (sym := spqrMlkemEncaps2Sym) hencaps2)
    (spqr_hook_ok_of_mem (sym := spqrLibcruxHmacSym) hhmac)
    ((spqr_externAt?_of_mem).trans h_panic)

theorem unchunked_ct1_sent_ek_received_send_ct2_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {H : String → Option (State → State)}
    (h_res : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 320) (doReserveSpec A))
    (h_concat3 : subroutine_ok ((blkPC_347).rebase (blkPl_347).base H)
      (lsmpl.base 386) (sliceConcat3Spec A))
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H spqrRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hencaps2 : HookSat H spqrMlkemEncaps2Sym (mlkemEncaps2Spec K))
    (hhmac : HookSat H spqrLibcruxHmacSym (libcruxHmacSpec F A)) :
    subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
      (withLsCodeLoaded lsmpl (unchunkedCt1SentEkReceivedSendCt2PlacedSpec A F K)) := by
  refine subroutine_ok_mono
    (unchunked_ct1_sent_ek_received_send_ct2_placed_ok
      h_res h_concat3 h_panic hshim halloc hdealloc hmemcpy hencaps2 hhmac)
    (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2

end CryptoVerification.SpqrV1.Unchunked
