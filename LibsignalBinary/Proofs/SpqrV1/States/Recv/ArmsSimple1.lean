/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `KeysUnsampled` Arm & Shared `Ok(V1Recv)` Epilogue

**Checked by Lean.** Offset-normalized word-grid combinators, the shared `+18996` `Ok(V1Recv)`
exit when `key = none` (`488`-byte variants), and the `States.keysUnsampled` arm (`0x554b4`, `+96`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Top CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `States.keysUnsampled` (`tag = 2#64`, `+96` / `0x554b4`) -/

theorem chunkedStatesAt_keysUnsampled_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) =
      (a ↦₆₄ 2#64) ∗ authenticatorAt A (a + 8#64) st.uc.auth ∗ ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 := by
  simp only [chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt,
    BitVec.add_assoc, show (8#64 + 48#64 : BitVec 64) = 56#64 from rfl]; ac_rfl

theorem chunkedStatesAt_keysUnsampled_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) ⊢
      ∃∗ g : TwoVecGhost,
        (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  have hauth : authenticatorAt A (a + 8#64) st.uc.auth =
      protoAuthenticatorAt A (a + 8#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩ := rfl
  rw [chunkedStatesAt_keysUnsampled_unfold, hauth]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (protoAuthenticatorAt_entails_dealloc A (a + 8#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  rw [sepConj_assoc (⌜g.v1.cap.toNat < 2 ^ 63⌝), sepConj_left_comm (a ↦₆₄ 2#64)]
  apply Entails.pure_left; intro _; refine Entails.sepExists_right g ?_
  simp only [twoVecHeadersAt, BitVec.add_assoc,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (8#64 + 16#64 : BitVec 64) = 24#64 from rfl,
    show (8#64 + 24#64 : BitVec 64) = 32#64 from rfl, show (8#64 + 32#64 : BitVec 64) = 40#64 from rfl,
    show (8#64 + 40#64 : BitVec 64) = 48#64 from rfl]; exact Entails.of_eq (by ac_rfl)

theorem keysUnsampled_selfA_err_combine (a c1 p1 c2 p2 ep : BitVec 64) :
    (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ p1) ∗ memRegion (a + 24#64) 8 ∗
    ((a + 32#64) ↦₆₄ c2) ∗ ((a + 40#64) ↦₆₄ p2) ∗ memRegion (a + 48#64) 8 ∗
    ((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864 ⊢ memRegion a chunkedStatesSize := by
  have h56 : ((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864 ⊢ memRegion (a + 56#64) 872 := by
    rw [ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 864) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 56#64) ep)
  have hhdr : twoVecHeadersAt (a + 8#64) ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ⊢ memRegion (a + 8#64) 48 :=
    twoVecHeadersAt_entails_memRegion_48 (a + 8#64) ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩
  simp only [twoVecHeadersAt, BitVec.add_assoc,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (8#64 + 16#64 : BitVec 64) = 24#64 from rfl,
    show (8#64 + 24#64 : BitVec 64) = 32#64 from rfl, show (8#64 + 32#64 : BitVec 64) = 40#64 from rfl,
    show (8#64 + 40#64 : BitVec 64) = 48#64 from rfl] at hhdr
  have h8 : memRegion (a + 8#64) 48 ∗ memRegion (a + 56#64) 872 ⊢ memRegion (a + 8#64) 920 := by
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 872) (b' := a + 56#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
  unfold chunkedStatesSize; rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 920) (b' := a + 8#64) rfl rfl (by decide)]
  refine Entails.trans (Entails.of_eq (show _ = (a ↦₆₄ 2#64) ∗
    ((((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ p1) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ c2) ∗ ((a + 40#64) ↦₆₄ p2) ∗ memRegion (a + 48#64) 8) ∗
     (((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864)) by ac_rfl)) ?_
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a 2#64) (Entails.trans (sepConj_mono hhdr h56) h8)

theorem memRegion_4088_split_456_504 (fsp : BitVec 64) :
    memRegion (fsp + 56#64) 4088 =
      memRegion (fsp + 56#64) 400 ∗ (∃∗ v456 : BitVec 64, ((fsp + 456#64) ↦₆₄ v456)) ∗
      memRegion (fsp + 464#64) 40 ∗ (∃∗ v504 : BitVec 64, ((fsp + 504#64) ↦₆₄ v504)) ∗ memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 56#64) (n := 400) (k := 3688) (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 8) (k := 3680) (b' := fsp + 464#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 456#64),
      ProofLib.memRegion_split' (b := fsp + 464#64) (n := 40) (k := 3640) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 504#64)]

theorem cells_456_504_entails_memRegion_4088 (fsp v456 v504 : BitVec 64) :
    memRegion (fsp + 56#64) 400 ∗ ((fsp + 456#64) ↦₆₄ v456) ∗
      memRegion (fsp + 464#64) 40 ∗ ((fsp + 504#64) ↦₆₄ v504) ∗ memRegion (fsp + 512#64) 3632 ⊢ memRegion (fsp + 56#64) 4088 := by
  rw [ProofLib.memRegion_split' (b := fsp + 56#64) (n := 400) (k := 3688) (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 8) (k := 3680) (b' := fsp + 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 464#64) (n := 40) (k := 3640) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 456#64) v456)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 504#64) v504))))

theorem ule_false_of_gt {a b : BitVec 64} (h : a > b) : BitVec.ule a b = false := by have hlt : b < a := h; bv_kernel
theorem ule_true_of_not_gt {a b : BitVec 64} (h : ¬ (a > b)) : BitVec.ule a b = true := by
  have hle : a ≤ b := by change ¬ (b < a) at h; bv_omega
  bv_kernel
theorem ne_zero_of_beq_false {c : BitVec 64} (h : (c == 0#64) = false) : c.toNat ≠ 0 := by
  intro h0; have hc : c = 0#64 := BitVec.eq_of_toNat_eq h0; subst hc; contradiction

theorem keysUnsampled_err_step_96_176
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s : State) (fsp outA selfA msgA st_epoch msg_epoch v_out0 v_out16 v_fsp456 v_fsp504 : BitVec 64)
    (b_out8 : BitVec 8) (g : TwoVecGhost) (Frame : SepProp)
    (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 176#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
        ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
       vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗
       stackAt fsp allocHookStack ∗ ((fsp + 456#64) ↦₆₄ v_fsp456) ∗ ((fsp + 504#64) ↦₆₄ v_fsp504) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
          (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
           ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
          (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
          ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st_epoch) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x0 = g.v2.ptr ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName +
        bv% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := by
    have h := hA.dealloc_ok_at statesRecvName
      (num% (ls_rel% "<spqr::v1::chunked::states::States>::recv" "__rustc::__rust_dealloc"))
    simpa only [contractProg, rustDeallocSpec] using h
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  states_recv_fetches_range b (Rust.withPanics ext) 96 80
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp hx19 hx1 hx24; dsimp only [vecCapPtrDealloc, noneCap]
  by_cases hc1 : (g.v1.cap == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · wp_steps; wp_apply; wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

set_option maxHeartbeats 1200000 in
/-- Error branch (`msg.epoch > st.uc.epoch`) of `States.keysUnsampled` (`+96 -> s0.readReg64 .x30`). -/
theorem states_recv_keysUnsampled_err_96
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, Chunked.SendEk.KeysUnsampled.epoch, Unchunked.SendEk.KeysUnsampled.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, memRegion_4088_split_456_504 fsp, stackAt_statesRecvCallee_eq_allocHook fsp]
  refine SepWP.fold (chunkedStatesAt_keysUnsampled_entails_dealloc A selfA st) (by sep_focus) ?_
  unfold messageAt; wp_pull_exists; rename_i v_fsp504 v_fsp456 v_out16 b_out8 v_out0 g
  have hstep1 := keysUnsampled_err_step_96_176 hA s fsp outA selfA msgA st.uc.epoch msg.epoch
    v_out0 v_out16 v_fsp456 v_fsp504 b_out8 g
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
     (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
     memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗
     memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
     memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
     statesRecvSavedCells s0) hgt hfsp_align hpc hrun hsp hx19 hx1 hx24
  refine seq_clean (mid := (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 176#64)
    (P_mid :=
      ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg.epoch)) ∗
      (((selfA + 8#64) ↦₆₄ g.v1.cap) ∗ ((selfA + 16#64) ↦₆₄ g.v1.ptr) ∗
       ((selfA + 32#64) ↦₆₄ g.v2.cap) ∗ ((selfA + 40#64) ↦₆₄ g.v2.ptr) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch)) ∗
      (msgA ↦₆₄ msg.epoch) ∗ A.pool ∗ stackAt fsp allocHookStack ∗
      ((fsp + 456#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 504#64) ↦₆₄ st.uc.epoch) ∗
      (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
       (selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 24#64) 8 ∗ memRegion (selfA + 48#64) 8 ∗
       memRegion (selfA + 64#64) 864 ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
       messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoAt b ∗
       memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗
       memRegion (fsp + 56#64) 400 ∗ memRegion (fsp + 464#64) 40 ∗ memRegion (fsp + 512#64) 3632 ∗
       statesRecvSavedCells s0))
    (Q := fun sm => sm.sp = fsp ∧ sm.readReg64 .x0 = g.v2.ptr ∧ sm.readReg64 .x29 = s0.sp - 96#64 ∧ TraceCalleeSaved sm s0)
    (by unfold TraceCalleeSaved at hstep1 ⊢; rw [hx29, htr.1, htr.2] at hstep1; exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx29_1, htr1⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch) (by sep_focus) ?_
  refine SepWP.fold (keysUnsampled_selfA_err_combine selfA g.v1.cap g.v1.ptr g.v2.cap g.v2.ptr st.uc.epoch) (by sep_focus) ?_
  have hepil_fn := @states_recv_epilogue_19324 b ext s0
  have htail_fn := @states_recv_tail_dealloc_192 A b ext hA s0
  states_recv_fetches_range b (Rust.withPanics ext) 176 16
  dsimp only [tripleRatchetProgAtExt, statesRecvName, BitVec.ofNat_eq_ofNat] at hpc1 hepil_fn htail_fn ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp1; dsimp only [vecCapPtrDealloc]
  by_cases hc2 : (g.v2.cap == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    refine SepWP.fold (cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch) (by sep_focus) ?_
    refine SepWP.fold (cell48_4088_entails_memRegion_4144 s1.sp v48) (by sep_focus) ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (hepil_fn _
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
      hsp0_align rfl (by simpa only [arm64_norm] using hrun1)
      (by simpa only [State.sp, arm64_norm] using hfsp_eq) ⟨by simpa only [arm64_norm] using htr1.1, by simpa only [arm64_norm] using htr1.2⟩))
      fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ⟨Entails.trans hPf (Entails.of_eq (by unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩
    rw [← hfsp_eq]; exact Entails.of_eq (by unfold messageAt; ac_rfl)
  · wp_steps
    refine SepWP.fold (cells_456_504_entails_memRegion_4088 s1.sp g.v2.cap st.uc.epoch) (by sep_focus) ?_
    refine SepWP.fold (cell48_4088_entails_memRegion_4144 s1.sp v48) (by sep_focus) ?_
    refine SepWP.mono (SepWP.weaken_pre ?_ (htail_fn _ g.v2.ptr g.v2.cap
      (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b)
      hsp0_align rfl (by simpa only [arm64_norm] using hrun1)
      (by simpa only [State.sp, arm64_norm] using hfsp_eq) (by simpa only [arm64_norm] using hx0_1) rfl rfl
      (ne_zero_of_beq_false (Bool.eq_false_iff.mpr hc2)) ⟨by simpa only [arm64_norm] using htr1.1, by simpa only [arm64_norm] using htr1.2⟩))
      fun sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩ => ⟨Entails.trans hPf (Entails.of_eq (by unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩
    rw [← hfsp_eq]; exact Entails.of_eq (by unfold messageAt; ac_rfl)

/-! ### Offset-Normalized Word-Grid Split & Recombine Combinators -/

/-- `n` existentially quantified 64-bit word cells at `(base + (k + 8 * i)#64)`. -/
def existsWordsAtOff (base : BitVec 64) : Nat → Nat → SepProp
  | 0, _ => emp
  | n + 1, k => (∃∗ w : BitVec 64, (base + BitVec.ofNat 64 k) ↦₆₄ w) ∗ existsWordsAtOff base n (k + 8)

theorem memRegion_off_eq_existsWordsAtOff (base : BitVec 64) :
    ∀ (n k : Nat), 8 * n ≤ 2 ^ 64 → memRegion (base + BitVec.ofNat 64 k) (8 * n) = existsWordsAtOff base n k
  | 0, k, _ => by simp [existsWordsAtOff, ProofLib.memRegion_zero]
  | n + 1, k, hn => by
    have hsplit : memRegion (base + BitVec.ofNat 64 k) (8 * (n + 1)) =
        memRegion (base + BitVec.ofNat 64 k) 8 ∗ memRegion (base + BitVec.ofNat 64 (k + 8)) (8 * n) := by
      refine ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 k) (n := 8) (k := 8 * n)
        (b' := base + BitVec.ofNat 64 (k + 8)) (by omega) ?_ (by omega)
      rw [BitVec.ofNat_add]; bv_omega
    rw [hsplit, ProofLib.memRegion_eight (base + BitVec.ofNat 64 k),
        memRegion_off_eq_existsWordsAtOff base n (k + 8) (by omega), existsWordsAtOff]

/-- Contiguous 64-bit word cells at `(base + (k + 8 * i)#64)`. -/
def wordsAtOff (base : BitVec 64) : List (BitVec 64) → Nat → SepProp
  | [], _ => emp
  | w :: ws, k => ((base + BitVec.ofNat 64 k) ↦₆₄ w) ∗ wordsAtOff base ws (k + 8)

theorem wordsAtOff_eq_wordsAt (base : BitVec 64) :
    ∀ (ws : List (BitVec 64)) (k : Nat), wordsAtOff base ws k = wordsAt (base + BitVec.ofNat 64 k) ws
  | [], k => rfl
  | w :: ws, k => by
    simp only [wordsAtOff, wordsAt]
    have haddr : base + BitVec.ofNat 64 (k + 8) = (base + BitVec.ofNat 64 k) + 8#64 := by rw [BitVec.ofNat_add]; bv_omega
    rw [wordsAtOff_eq_wordsAt base ws (k + 8), haddr]

theorem wordsAtOff_entails_memRegion (base : BitVec 64) (ws : List (BitVec 64)) (k n : Nat)
    (hn : 8 * ws.length = n) : wordsAtOff base ws k ⊢ memRegion (base + BitVec.ofNat 64 k) n := by
  rw [wordsAtOff_eq_wordsAt]; exact wordsAt_entails_memRegion ws (base + BitVec.ofNat 64 k) n hn

theorem wordsAtOff_entails_memRegion_zero (base : BitVec 64) (ws : List (BitVec 64)) (n : Nat)
    (hn : 8 * ws.length = n) : wordsAtOff base ws 0 ⊢ memRegion base n := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using wordsAtOff_entails_memRegion base ws 0 n hn

/-- Stack cells in `fsp + 224..504` read by Step A (`+18996 -> +19128`), excluding `q960`. -/
def epilogueRecvStackPartA488 (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64) : SepProp :=
  ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
  ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 368#64) ↦₆₄ w368) ∗
  ((fsp + 376#64) ↦₆₄ w376) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗ ((fsp + 408#64) ↦₆₄ w408) ∗
  ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ w456) ∗ ((fsp + 496#64) ↦₆₄ w496) ∗ ((fsp + 504#64) ↦₆₄ w504)

theorem epilogueRecvStackPartA_eq_488 (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64) (q960 : BitVec 128) :
    epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 =
      epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 960#64) ↦₁₂₈ q960) := by
  simp only [epilogueRecvStackPartA, epilogueRecvStackPartA488, sepConj_assoc]

/-- First 30 words (`out + 120..480`) written in Step B (`+19128 -> +19280`). -/
def epilogueRecvOutPartB488 (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) : SepProp :=
  ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
  ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
  ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
  ((out + 216#64) ↦₆₄ w216) ∗ ((out + 224#64) ↦₆₄ w224) ∗ ((out + 232#64) ↦₆₄ w232) ∗ ((out + 240#64) ↦₆₄ w240) ∗
  ((out + 248#64) ↦₆₄ w248) ∗ ((out + 256#64) ↦₆₄ w256) ∗ ((out + 360#64) ↦₆₄ w360) ∗ ((out + 368#64) ↦₆₄ w368) ∗
  ((out + 376#64) ↦₆₄ w376) ∗ ((out + 384#64) ↦₆₄ w384) ∗ ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480)

theorem epilogueRecvOutPartB_eq_488 (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) (q488 : BitVec 128) (w504 : BitVec 64) :
    epilogueRecvOutPartB out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 q488 w504 =
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ∗
      ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w504) := by
  simp only [epilogueRecvOutPartB, epilogueRecvOutPartB488, sepConj_assoc]

theorem epilogueStack_224_512_entails_memRegion (fsp : BitVec 64)
    (w224 w232 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64) :
    epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
      epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ⊢
    memRegion (fsp + 224#64) 288 := by
  refine Entails.trans (Entails.of_eq ?_)
    (wordsAtOff_entails_memRegion fsp
      [w224, w232, w240, w248, w256, w264, w272, w280, w288, w296, w304, w312,
       w320, w328, w336, w344, w352, w360, w368, w376, w384, w392, w400, w408,
       w416, w424, w432, w440, w448, w456, w464, w472, w480, w488, w496, w504] 224 288 rfl)
  dsimp only [wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem epilogueOut_64_488_entails_words_and_memRegion (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) :
    epilogueRecvOutPartA out w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112
      w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ⊢
    (out ↦₆₄ w0) ∗ wordsAt (out + 8#64) [w8, w16, w24, w32, w40, w48] ∗ ((out + 56#64) ↦₆₄ w56) ∗ memRegion (out + 64#64) 424 := by
  have h53 : wordsAtOff out
      [w64, w72, w80, w88, w96, w104, w112,
       w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208, w216, w224, w232, w240, w248, w256,
       w264, w272, w280, w288, w296, w304, w312, w320, w328, w336, w344, w352,
       w360, w368, w376, w384, w392, w400, w408, w416, w424, w432, w440, w448, w456, w464, w472, w480]
      64 ⊢ memRegion (out + 64#64) 424 := wordsAtOff_entails_memRegion out _ 64 424 rfl
  rw [(wordsAtOff_eq_wordsAt out [w8, w16, w24, w32, w40, w48] 8).symm]
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h53)))
  dsimp only [wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem memRegion_entails_exists_pointsToBytes :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 → (memRegion a n ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (a ↦ₛ bs))
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]; refine Entails.sepExists_right [] ?_
    rw [pointsToBytes_nil]; exact Entails.pure_right rfl (Entails.refl _)
  | n + 1, a, hn => by
    rw [show n + 1 = 1 + n by omega, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a]
    refine Entails.trans (sepConj_mono_right (memRegion_entails_exists_pointsToBytes n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [← sepConj_assoc, sepConj_comm (a ↦₈ b0), sepConj_assoc]; apply Entails.pure_left; intro hbs
    refine Entails.sepExists_right (b0 :: bs) (Entails.pure_right (by simp [hbs]; omega) ?_)
    rw [pointsToBytes_cons]; exact Entails.refl _

theorem pointsToBytes_entails_memRegion' :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64), bs.length ≤ 2 ^ 64 → ((a ↦ₛ bs) ⊢ memRegion a bs.length)
  | [], a, _ => by rw [pointsToBytes_nil, List.length_nil, ProofLib.memRegion_zero]; exact Entails.refl _
  | b0 :: bs, a, hbs => by
    simp only [List.length_cons] at hbs ⊢
    rw [show bs.length + 1 = 1 + bs.length by omega, ProofLib.memRegion_split a 1 bs.length (by omega), pointsToBytes_cons]
    exact sepConj_mono (ProofLib.pointsTo8_entails_memRegion a b0) (pointsToBytes_entails_memRegion' bs (a + 1#64) (by omega))

theorem pointsToBytes_entails_memRegion_len (a : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hn : bs.length = n) (hbound : n ≤ 2 ^ 64) : (a ↦ₛ bs) ⊢ memRegion a n := by
  subst hn; exact pointsToBytes_entails_memRegion' bs a hbound

theorem memRegion_3632_entails_epilogue (fsp : BitVec 64) :
    memRegion (fsp + 512#64) 3632 ⊢
      ((∃∗ q512 : BitVec 128, (fsp + 512#64) ↦₁₂₈ q512) ∗ (∃∗ q528 : BitVec 128, (fsp + 528#64) ↦₁₂₈ q528) ∗
       (∃∗ q544 : BitVec 128, (fsp + 544#64) ↦₁₂₈ q544) ∗ (∃∗ w560 : BitVec 64, (fsp + 560#64) ↦₆₄ w560) ∗
       (∃∗ bs576 : List (BitVec 8), ⌜bs576.length = 376⌝ ∗ ((fsp + 576#64) ↦ₛ bs576)) ∗
       (∃∗ q960 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q960)) ∗
      (memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 512#64),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 3600) (b' := fsp + 544#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 528#64),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 3584) (b' := fsp + 560#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 544#64),
      ProofLib.memRegion_split' (b := fsp + 560#64) (n := 8) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 560#64),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 960#64)]
  exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_entails_exists_pointsToBytes 376 (fsp + 576#64) (by decide))))))))
    (Entails.of_eq (by ac_rfl))

theorem epilogue_entails_memRegion_3632 (fsp : BitVec 64)
    (q512 q528 q544 q960 : BitVec 128) (w560 : BitVec 64) (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376) :
    ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗
      ((fsp + 560#64) ↦₆₄ w560) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗
      memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗ memRegion (fsp + 976#64) 3168 ⊢
    memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 512#64),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 3600) (b' := fsp + 544#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 528#64),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 3584) (b' := fsp + 560#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 544#64),
      ProofLib.memRegion_split' (b := fsp + 560#64) (n := 8) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 560#64),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 960#64)]
  exact sepConj_mono (Entails.sepExists_right q512 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right q528 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right q544 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w560 (Entails.refl _))
          (sepConj_mono_right (sepConj_mono
            (pointsToBytes_entails_memRegion_len (fsp + 576#64) bs576 376 hbs576 (by decide))
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right q960 (Entails.refl _)))))))))

theorem memRegion_472_entails_epilogue (out : BitVec 64) :
    memRegion (out + 488#64) 472 ⊢
      ((∃∗ uq488 : BitVec 128, (out + 488#64) ↦₁₂₈ uq488) ∗ (∃∗ u504 : BitVec 64, (out + 504#64) ↦₆₄ u504) ∗
       (∃∗ uq888 : BitVec 128, (out + 888#64) ↦₁₂₈ uq888) ∗ (∃∗ uq904 : BitVec 128, (out + 904#64) ↦₁₂₈ uq904) ∗
       (∃∗ u920 : BitVec 64, (out + 920#64) ↦₆₄ u920) ∗ (∃∗ u928 : BitVec 64, (out + 928#64) ↦₆₄ u928) ∗
       (∃∗ u936 : BitVec 64, (out + 936#64) ↦₆₄ u936) ∗ (∃∗ uq944 : BitVec 128, (out + 944#64) ↦₁₂₈ uq944)) ∗
      memRegion (out + 512#64) 376 := by
  rw [ProofLib.memRegion_split' (b := out + 488#64) (n := 16) (k := 456) (b' := out + 504#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 488#64),
      ProofLib.memRegion_split' (b := out + 504#64) (n := 8) (k := 448) (b' := out + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 504#64),
      ProofLib.memRegion_split' (b := out + 512#64) (n := 376) (k := 72) (b' := out + 888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 888#64) (n := 16) (k := 56) (b' := out + 904#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 888#64),
      ProofLib.memRegion_split' (b := out + 904#64) (n := 16) (k := 40) (b' := out + 920#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 904#64),
      ProofLib.memRegion_split' (b := out + 920#64) (n := 8) (k := 32) (b' := out + 928#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 920#64),
      ProofLib.memRegion_split' (b := out + 928#64) (n := 8) (k := 24) (b' := out + 936#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 928#64),
      ProofLib.memRegion_split' (b := out + 936#64) (n := 8) (k := 16) (b' := out + 944#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 936#64), ProofLib.memRegion_sixteen (out + 944#64)]
  exact Entails.of_eq (by ac_rfl)

theorem epilogue_out_488_960_entails_memRegion_and_optNone (A : RustAlloc) (out : BitVec 64)
    (q488 q528 q544 q512 : BitVec 128) (w256 w560 w936 : BitVec 64) (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376) :
    ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
      ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗
      ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512) ⊢
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none := by
  have h440 : ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
      ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ⊢ memRegion (out + 488#64) 440 := by
    rw [ProofLib.memRegion_split' (b := out + 488#64) (n := 16) (k := 424) (b' := out + 504#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 488#64),
        ProofLib.memRegion_split' (b := out + 504#64) (n := 8) (k := 416) (b' := out + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 504#64),
        ProofLib.memRegion_split' (b := out + 512#64) (n := 376) (k := 40) (b' := out + 888#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 888#64) (n := 16) (k := 24) (b' := out + 904#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 888#64),
        ProofLib.memRegion_split' (b := out + 904#64) (n := 16) (k := 8) (b' := out + 920#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_sixteen (out + 904#64), ProofLib.memRegion_eight (out + 920#64)]
    exact sepConj_mono (Entails.sepExists_right q488 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w256 (Entails.refl _))
        (sepConj_mono (pointsToBytes_entails_memRegion_len (out + 512#64) bs576 376 hbs576 (by decide))
          (sepConj_mono (Entails.sepExists_right q528 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right q544 (Entails.refl _)) (Entails.sepExists_right w560 (Entails.refl _))))))
  have h24 : ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512) ⊢ optEpochSecretAt A (out + 928#64) none := by
    rw [optEpochSecretAt_none, BitVec.add_assoc, show (928#64 + 8#64 : BitVec 64) = 936#64 from rfl,
        ProofLib.memRegion_split' (b := out + 936#64) (n := 8) (k := 16) (b' := out + 944#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (out + 936#64), ProofLib.memRegion_sixteen (out + 944#64)]
    exact sepConj_mono_right (sepConj_mono (Entails.sepExists_right w936 (Entails.refl _)) (Entails.sepExists_right q512 (Entails.refl _)))
  exact Entails.trans (Entails.of_eq (show _ =
    (((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
     ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560)) ∗
    (((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512)) by ac_rfl))
    (sepConj_mono h440 h24)

theorem wordsAtOff_out_488_eq_epilogueOut (out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : BitVec 64)
    (u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 : BitVec 64)
    (u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 : BitVec 64)
    (u360 u368 u376 u384 u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 : BitVec 64) :
    wordsAtOff out
      [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112,
       u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216, u224, u232, u240, u248, u256,
       u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352,
       u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480] 0 =
    epilogueRecvOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
      u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 ∗
    epilogueRecvOutPartB488 out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
      u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 := by
  dsimp only [wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  rw [BitVec.add_zero]; ac_rfl

theorem stack_recombine_4144 (fsp : BitVec 64) :
    memRegion fsp 224 ∗ memRegion (fsp + 224#64) 288 ∗ memRegion (fsp + 512#64) 3632 = memRegion fsp 4144 := by
  rw [ProofLib.memRegion_split fsp 224 3920 (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 288) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide)]

theorem memRegion_out_960_split_488_472 (out : BitVec 64) :
    memRegion out v1RecvSize = memRegion out 488 ∗ memRegion (out + 488#64) 472 := by
  unfold v1RecvSize; exact ProofLib.memRegion_split out 488 472 (by decide)

theorem sepWP_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog target_pc s P post) : SepWP prog target_pc s (⌜φ⌝ ∗ P) post :=
  SepWP.pure_elim h

theorem sepWP_intro_ex {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {Q : α → SepProp}
    (h : ∀ v : α, SepWP prog target_pc s (rest ∗ (Q v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, Q v) ∗ rest) ∗ R) post := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro v; rw [sepConj_assoc, sepConj_left_comm (Q v)]; exact h v

theorem sepWP_intro_ex_pure {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {φ : α → Prop} {Q : α → SepProp}
    (h : ∀ v : α, φ v → SepWP prog target_pc s (rest ∗ (Q v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, ⌜φ v⌝ ∗ Q v) ∗ rest) ∗ R) post := by
  apply sepWP_intro_ex; intro v
  rw [sepConj_assoc (⌜φ v⌝), sepConj_left_comm rest (⌜φ v⌝)]; exact sepWP_pure_left (h v)

theorem relocatedHeap_recompose_words (F : BitVec 64 → SepProp) (ws : List (BitVec 64)) (dst : BitVec 64) :
    wordsAt dst ws ∗ relocatedHeap F (wordsBytes ws) ⊢ F dst := by
  rw [wordsAt_eq_pointsToBytes ws dst]; exact relocatedHeap_recompose F (wordsBytes ws) dst

theorem selfA_8words_entails_memRegion_928 (selfA w0 w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (selfA ↦₆₄ w0) ∗ ((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
    ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗
    ((selfA + 56#64) ↦₆₄ w56) ∗ memRegion (selfA + 64#64) 864 ⊢ memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize; rw [ProofLib.memRegion_split selfA 64 864 (by decide)]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_left (wordsAtOff_entails_memRegion_zero selfA [w0, w8, w16, w24, w32, w40, w48, w56] 64 rfl))
  dsimp only [wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]; ac_rfl

theorem resultV1RecvAt_ok (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) :
    resultV1RecvAt A (F := F) out (.ok v) =
      chunkedStatesAt A out v.state ∗ optEpochSecretAt A (out + 928#64) v.key := rfl

set_option maxHeartbeats 1600000 in
/-- Shared `Ok(V1Recv)` exit from `+18996` (`0x59e88 -> s0.readReg64 .x30`) when `key = none`
    (`[fsp + 232] = noneCap`) and the output `States` variant fits in the first 488 bytes of `out`. -/
theorem epilogue_18996_exit_none_488
    {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (s0 s1 : State) (out : BitVec 64)
    (w224 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Rest : SepProp) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx19 : s1.readReg64 .x19 = out) (htr1 : TraceCalleeSaved s1 s0) :
    let fsp := s0.sp - 4240#64
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s1
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion out v1RecvSize ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢
          epilogueRecvOutPartA out
            w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
            (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
            (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
            (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
            (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
          epilogueRecvOutPartB488 out
            w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
            w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
            w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
          memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  intro fsp
  have hfsp_align : (fsp &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hout0 : memRegion out 488 = existsWordsAtOff out 61 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul] using memRegion_off_eq_existsWordsAtOff out 61 0 (by decide)
  rw [memRegion_out_960_split_488_472 out, hout0]
  have hpre :
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗
       (existsWordsAtOff out 61 0 ∗ memRegion (out + 488#64) 472) ∗ Rest ⊢
      ((∃∗ q512 : BitVec 128, (fsp + 512#64) ↦₁₂₈ q512) ∗ (∃∗ q528 : BitVec 128, (fsp + 528#64) ↦₁₂₈ q528) ∗
       (∃∗ q544 : BitVec 128, (fsp + 544#64) ↦₁₂₈ q544) ∗ (∃∗ w560 : BitVec 64, (fsp + 560#64) ↦₆₄ w560) ∗
       (∃∗ bs576 : List (BitVec 8), ⌜bs576.length = 376⌝ ∗ ((fsp + 576#64) ↦ₛ bs576)) ∗
       (∃∗ q960 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q960) ∗ (∃∗ uq488 : BitVec 128, (out + 488#64) ↦₁₂₈ uq488) ∗
       (∃∗ u504 : BitVec 64, (out + 504#64) ↦₆₄ u504) ∗ (∃∗ uq888 : BitVec 128, (out + 888#64) ↦₁₂₈ uq888) ∗
       (∃∗ uq904 : BitVec 128, (out + 904#64) ↦₁₂₈ uq904) ∗ (∃∗ u920 : BitVec 64, (out + 920#64) ↦₆₄ u920) ∗
       (∃∗ u928 : BitVec 64, (out + 928#64) ↦₆₄ u928) ∗ (∃∗ u936 : BitVec 64, (out + 936#64) ↦₆₄ u936) ∗
       (∃∗ uq944 : BitVec 128, (out + 944#64) ↦₁₂₈ uq944) ∗ existsWordsAtOff out 61 0) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_3632_entails_epilogue fsp)
        (sepConj_mono_right (sepConj_mono_left (sepConj_mono_right (memRegion_472_entails_epilogue out)))))))))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]
  apply sepWP_intro_ex; intro q512; apply sepWP_intro_ex; intro q528; apply sepWP_intro_ex; intro q544; apply sepWP_intro_ex; intro w560
  apply sepWP_intro_ex_pure; intro bs576 hbs576; apply sepWP_intro_ex; intro q960; apply sepWP_intro_ex; intro uq488; apply sepWP_intro_ex; intro u504
  apply sepWP_intro_ex; intro uq888; apply sepWP_intro_ex; intro uq904; apply sepWP_intro_ex; intro u920; apply sepWP_intro_ex; intro u928
  apply sepWP_intro_ex; intro u936; apply sepWP_intro_ex; intro uq944
  apply sepWP_intro_ex; intro u0; apply sepWP_intro_ex; intro u8; apply sepWP_intro_ex; intro u16; apply sepWP_intro_ex; intro u24; apply sepWP_intro_ex; intro u32; apply sepWP_intro_ex; intro u40
  apply sepWP_intro_ex; intro u48; apply sepWP_intro_ex; intro u56; apply sepWP_intro_ex; intro u64; apply sepWP_intro_ex; intro u72; apply sepWP_intro_ex; intro u80; apply sepWP_intro_ex; intro u88
  apply sepWP_intro_ex; intro u96; apply sepWP_intro_ex; intro u104; apply sepWP_intro_ex; intro u112; apply sepWP_intro_ex; intro u120; apply sepWP_intro_ex; intro u128; apply sepWP_intro_ex; intro u136
  apply sepWP_intro_ex; intro u144; apply sepWP_intro_ex; intro u152; apply sepWP_intro_ex; intro u160; apply sepWP_intro_ex; intro u168; apply sepWP_intro_ex; intro u176; apply sepWP_intro_ex; intro u184
  apply sepWP_intro_ex; intro u192; apply sepWP_intro_ex; intro u200; apply sepWP_intro_ex; intro u208; apply sepWP_intro_ex; intro u216; apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232
  apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264; apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280
  apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312; apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328
  apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360; apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376
  apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408; apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424
  apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456; apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472
  apply sepWP_intro_ex; intro u480; rw [emp_sepConj]
  have hstepA := epilogue_step_18996_19128 (b := b) (ext := ext) s1 fsp out
    u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
    u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432
    w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960
    (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
     memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
     statesRecvSavedCells s0 ∗
     epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
       u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
     memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
     ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
    hfsp_align hpc1 hrun1 hsp1 hx19
  refine seq_clean (SepWP.weaken_pre ?_ hstepA) ?_
  · rw [epilogueRecvStackPartA_eq_488, epilogueRecvOutPartB_eq_488]; refine Entails.of_eq ?_
    trans (wordsAtOff out
      [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112,
       u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216, u224, u232, u240, u248, u256,
       u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352,
       u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480] 0 ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
       ((fsp + 960#64) ↦₁₂₈ q960) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ ((out + 488#64) ↦₁₂₈ uq488) ∗ ((out + 504#64) ↦₆₄ u504) ∗ memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗ ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest))
    · dsimp only [wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]; ac_rfl
    · rw [wordsAtOff_out_488_eq_epilogueOut]; ac_rfl
  · intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, hx3_2, hx16_2, hx17_2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx26_2, hx27_2, hx29_2, hv0_2, htr2⟩
    let outPartA := epilogueRecvOutPartA out
      w224 (s1.readReg64 .x1) (s1.readReg64 .x8) w496 w456 w376 w368 w504 w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
    have hstepB := epilogue_step_19128_19280 (b := b) (ext := ext) s2 fsp out
      u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
      u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504
      w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
      (outPartA ∗ epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168 ∗
       statesRecvSavedCells s0 ∗ memRegion (out + 512#64) 376 ∗ ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗ ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗ Rest)
      hfsp_align hpc2 hrun2 hsp2 hx0_2 hx1_2 hx19_2
    refine seq_clean (SepWP.weaken_pre (Entails.of_eq (by dsimp only [outPartA]; ac_rfl)) hstepB) ?_
    intro s3 hpc3 hrun3 ⟨hsp3, hx0_3, hx1_3, hx2_3, hx19_3, hx20_3, hx29_3, htr3⟩
    rw [hx23_2, hx27_2, hx3_2, hx24_2, hx17_2, hx26_2, hx22_2, hx16_2, hx2_2, hx20_2, hv0_2]
    let outPartB488 := epilogueRecvOutPartB488 out
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440 w264 w344 w392 w272 w360 w400 w464 w304
      w328 w280 w320 (s1.readReg64 .x3) w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    have hstepC := epilogue_step_19280_19324 hA s3 fsp out bs576 hbs576 uq888 uq904 uq944 q512 q528 q544 u920 u928 u936 noneCap w560
      (memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 224 ∗
       epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
       memRegion (fsp + 976#64) 3168 ∗ statesRecvSavedCells s0 ∗
       outPartA ∗ outPartB488 ∗ ((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ Rest)
      hfsp_align hpc3 hrun3 hsp3 hx0_3 hx1_3 hx2_3 hx19_3
    refine seq_clean (SepWP.weaken_pre ?_ hstepC) ?_
    · rw [epilogueRecvOutPartB_eq_488, epilogueRecvStackPartA_eq_488, stackAt_statesRecvCallee_eq_allocHook fsp]
      exact Entails.of_eq (by dsimp only [outPartB488]; ac_rfl)
    · intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
      have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans htr1))
      have hepil := states_recv_epilogue_19324 (b := b) (ext := ext) s0 s4
        (outPartA ∗ outPartB488 ∗ memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗ Rest)
        hsp0_align hpc4 hrun4 hsp4 htr40
      refine SepWP.mono (SepWP.weaken_pre ?_ hepil) ?_
      · have hstk288 := epilogueStack_224_512_entails_memRegion fsp
          w224 noneCap w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504
          w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
        have hstk3632 := epilogue_entails_memRegion_3632 fsp q512 q528 q544 q960 w560 bs576 hbs576
        have hout440 := epilogue_out_488_960_entails_memRegion_and_optNone A out q960 q528 q544 q512 w256 w560 (s3.readReg64 .x20) bs576 hbs576
        rw [← stack_recombine_4144 fsp, stackAt_statesRecvCallee_eq_allocHook fsp]
        refine Entails.trans (Entails.of_eq (show _ =
          (memRegion (fsp - 19552#64) 15456 ∗ stackAt fsp allocHookStack ∗ memRegion fsp 224) ∗
          (epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
           ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
           epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488) ∗
          (((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
           memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗ memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗
           memRegion (fsp + 976#64) 3168) ∗
          (statesRecvSavedCells s0 ∗ outPartA ∗ outPartB488) ∗
          (((out + 488#64) ↦₁₂₈ q960) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗ ((out + 888#64) ↦₁₂₈ q528) ∗
           ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ s3.readReg64 .x20) ∗
           ((out + 944#64) ↦₁₂₈ q512)) ∗ Rest by ac_rfl))
          (Entails.trans (sepConj_mono_right (sepConj_mono hstk288
            (sepConj_mono hstk3632 (sepConj_mono_right (sepConj_mono_left hout440))))) (Entails.of_eq (by ac_rfl)))
      · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
        exact ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [outPartA, outPartB488]; ac_rfl)), hsp_f, hcs_f, htr_f⟩

theorem keysUnsampled_ok_step_96_18996
    {b : BitVec 64} {ext : String → Option (State → State)} (s : State) (fsp outA selfA msgA : BitVec 64)
    (w8 w16 w24 w32 w40 w48 st_epoch msg_epoch u224 u232 u368 u376 u456 u496 u504 : BitVec 64) (Frame : SepProp)
    (hle : ¬ (msg_epoch > st_epoch)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 18996#64) s
      ((((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
        ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
       (msgA ↦₆₄ msg_epoch) ∗
       (((fsp + 224#64) ↦₆₄ u224) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗ ((fsp + 376#64) ↦₆₄ u376) ∗
        ((fsp + 456#64) ↦₆₄ u456) ∗ ((fsp + 496#64) ↦₆₄ u496) ∗ ((fsp + 504#64) ↦₆₄ u504)) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢
          (((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
           ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗ ((selfA + 56#64) ↦₆₄ st_epoch)) ∗
          (msgA ↦₆₄ msg_epoch) ∗
          (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 368#64) ↦₆₄ w48) ∗ ((fsp + 376#64) ↦₆₄ w40) ∗
           ((fsp + 456#64) ↦₆₄ w32) ∗ ((fsp + 496#64) ↦₆₄ w24) ∗ ((fsp + 504#64) ↦₆₄ st_epoch)) ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x1 = w8 ∧ sm.readReg64 .x8 = w16 ∧
        sm.readReg64 .x19 = outA ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch st_epoch = true := ule_true_of_not_gt hle
  states_recv_fetches_range b (Rust.withPanics ext) 96 36
  states_recv_fetches_range b (Rust.withPanics ext) 3772 44
  dsimp only [tripleRatchetProgAtExt, statesRecvName, noneCap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<spqr::v1::chunked::states::States>::recv" = entry
  examples_hide_fetches; subst hsp hx19 hx1 hx24; wp_steps; wp_done

theorem chunkedStatesAt_keysUnsampled_extract (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) ⊢
      ∃∗ g : AuthWords,
        (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ g.v1.w0) ∗ ((a + 16#64) ↦₆₄ g.v1.w1) ∗ ((a + 24#64) ↦₆₄ g.v1.w2) ∗
        ((a + 32#64) ↦₆₄ g.v2.w0) ∗ ((a + 40#64) ↦₆₄ g.v2.w1) ∗ ((a + 48#64) ↦₆₄ g.v2.w2) ∗
        ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 ∗
        relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) := by
  rw [chunkedStatesAt_keysUnsampled_unfold]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (authenticatorAt_extract A (a + 8#64) st.uc.auth))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro g; refine Entails.sepExists_right g ?_
  rw [← wordsAtOff_eq_wordsAt a (authWordsList g) 8]
  dsimp only [authWordsList, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl)

theorem keysUnsampled_out_recompose (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (g : AuthWords)
    (w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) :
    epilogueRecvOutPartA out 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ⊢
    resultV1RecvAt A (F := F) out (.ok ⟨none, .keysUnsampled st⟩) := by
  rw [resultV1RecvAt_ok, chunkedStatesAt_keysUnsampled_unfold,
      ProofLib.memRegion_split' (b := out + 64#64) (n := 424) (k := 440) (b' := out + 488#64) rfl (by bv_omega) (by decide)]
  have hout := epilogueOut_64_488_entails_words_and_memRegion out
    2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
    w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432
    w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
    w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480
  have hrec := relocatedHeap_recompose_words (fun dst => authenticatorAt A dst st.uc.auth) (authWordsList g) (out + 8#64)
  dsimp only [authWordsList] at hrec
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueRecvOutPartA out 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
       w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
     epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
       w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480) ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hout) (Entails.trans (Entails.of_eq (show _ =
      (out ↦₆₄ 2#64) ∗ (wordsAt (out + 8#64) [g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2] ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
      ((out + 56#64) ↦₆₄ st.uc.epoch) ∗ (memRegion (out + 64#64) 424 ∗ memRegion (out + 488#64) 440) ∗
      optEpochSecretAt A (out + 928#64) none by ac_rfl))
      (Entails.trans (sepConj_mono_right (sepConj_mono_left hrec)) (Entails.of_eq (by ac_rfl)))))

set_option maxHeartbeats 1600000 in
/-- Ok branch (`¬ (msg.epoch > st.uc.epoch)`) of `States.keysUnsampled` (`+96 -> s0.readReg64 .x30`). -/
theorem states_recv_keysUnsampled_ok_96
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s0 s : State) (fsp outA selfA msgA v48 : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName + 96#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx1 : s.readReg64 .x1 = selfA) (hx24 : s.readReg64 .x24 = msgA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.keysUnsampled st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.keysUnsampled st).recv K msg = .ok ⟨none, .keysUnsampled st⟩ := by
    simp only [States.recv, Chunked.SendEk.KeysUnsampled.epoch, Unchunked.SendEk.KeysUnsampled.epoch, hle, ↓reduceIte]
  rw [hrecv]
  have hstk288 : memRegion (fsp + 224#64) 288 = existsWordsAtOff fsp 36 224 :=
    memRegion_off_eq_existsWordsAtOff fsp 36 224 (by decide)
  have hpre :
      memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 48 ∗
       ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088 ∗ statesRecvSavedCells s0 ⊢
      ((∃∗ g : AuthWords,
          (selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗ ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗
          ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗ ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗
          ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864 ∗
          relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
       existsWordsAtOff fsp 36 224) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
       stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗
       statesRecvSavedCells s0) := by
    refine Entails.trans (Entails.of_eq (show _ =
      chunkedStatesAt A selfA (.keysUnsampled st) ∗
      (memRegion fsp 48 ∗ ((fsp + 48#64) ↦₆₄ v48) ∗ memRegion (fsp + 56#64) 4088) ∗
      (memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (chunkedStatesAt_keysUnsampled_extract A selfA st)
      (sepConj_mono_left (cell48_4088_entails_memRegion_4144 fsp v48))) ?_
    rw [← stack_recombine_4144 fsp, hstk288]; exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro w224; apply sepWP_intro_ex; intro w232; apply sepWP_intro_ex; intro w240; apply sepWP_intro_ex; intro w248; apply sepWP_intro_ex; intro w256; apply sepWP_intro_ex; intro w264
  apply sepWP_intro_ex; intro w272; apply sepWP_intro_ex; intro w280; apply sepWP_intro_ex; intro w288; apply sepWP_intro_ex; intro w296; apply sepWP_intro_ex; intro w304; apply sepWP_intro_ex; intro w312
  apply sepWP_intro_ex; intro w320; apply sepWP_intro_ex; intro w328; apply sepWP_intro_ex; intro w336; apply sepWP_intro_ex; intro w344; apply sepWP_intro_ex; intro w352; apply sepWP_intro_ex; intro w360
  apply sepWP_intro_ex; intro w368; apply sepWP_intro_ex; intro w376; apply sepWP_intro_ex; intro w384; apply sepWP_intro_ex; intro w392; apply sepWP_intro_ex; intro w400; apply sepWP_intro_ex; intro w408
  apply sepWP_intro_ex; intro w416; apply sepWP_intro_ex; intro w424; apply sepWP_intro_ex; intro w432; apply sepWP_intro_ex; intro w440; apply sepWP_intro_ex; intro w448; apply sepWP_intro_ex; intro w456
  apply sepWP_intro_ex; intro w464; apply sepWP_intro_ex; intro w472; apply sepWP_intro_ex; intro w480; apply sepWP_intro_ex; intro w488; apply sepWP_intro_ex; intro w496; apply sepWP_intro_ex; intro w504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := keysUnsampled_ok_step_96_18996 (b := b) (ext := ext) s fsp outA selfA msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch msg.epoch w224 w232 w368 w376 w456 w496 w504
    ((selfA ↦₆₄ 2#64) ∗ memRegion (selfA + 64#64) 864 ∗
     relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     ((fsp + 240#64) ↦₆₄ w240) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
     ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗
     ((fsp + 408#64) ↦₆₄ w408) ∗ ((fsp + 432#64) ↦₆₄ w432) ∗
     epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
     memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
     memRegion fsp 224 ∗ memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0)
    hle hfsp_align hpc hrun hsp hx19 hx1 hx24
  refine seq_clean (SepWP.weaken_pre (Entails.of_eq (by dsimp only [epilogueRecvStackPartB]; ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx1_1, hx8_1, hx19_1, hx29_1, htr1⟩
  have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
  have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
  have hexit := epilogue_18996_exit_none_488 hA s0 s1 outA
    2#64 w240 w288 w296 w336 w352 g.v2.w2 g.v2.w1 w384 w408 w432 g.v2.w0 g.v1.w2 st.uc.epoch
    w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488
    (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
     memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool)
    hsp0_align hpc1 hrun1 hsp10 hx19_1 htr10
  dsimp only at hexit; rw [← hfsp_eq] at hexit
  refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
  · have hself := selfA_8words_entails_memRegion_928 selfA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
    unfold messageAt epilogueRecvStackPartA488
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 2#64) ∗ ((selfA + 8#64) ↦₆₄ g.v1.w0) ∗ ((selfA + 16#64) ↦₆₄ g.v1.w1) ∗
       ((selfA + 24#64) ↦₆₄ g.v1.w2) ∗ ((selfA + 32#64) ↦₆₄ g.v2.w0) ∗ ((selfA + 40#64) ↦₆₄ g.v2.w1) ∗
       ((selfA + 48#64) ↦₆₄ g.v2.w2) ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (selfA + 64#64) 864) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
       (((fsp + 224#64) ↦₆₄ 2#64) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
        ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 368#64) ↦₆₄ g.v2.w2) ∗
        ((fsp + 376#64) ↦₆₄ g.v2.w1) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗ ((fsp + 408#64) ↦₆₄ w408) ∗
        ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ g.v2.w0) ∗ ((fsp + 496#64) ↦₆₄ g.v1.w2) ∗
        ((fsp + 504#64) ↦₆₄ st.uc.epoch)) ∗
       ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       memRegion (fsp + 512#64) 3632 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       (relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ∗
        ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
        statesRecvRoAt b ∗ A.pool)) by ac_rfl)) (Entails.trans (sepConj_mono_left hself) (Entails.of_eq (by ac_rfl)))
  · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
    rw [hx1_1, hx8_1] at hPf
    have hrec := keysUnsampled_out_recompose A outA st g w288 w432 w408 w352 w384 w336 w296
      (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
      (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
      (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
      (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14)
      w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
      w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
      w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
      w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20)
    refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
      (epilogueRecvOutPartA outA 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
         w288 w432 w408 w352 w384 w336 w296
         (s1.readReg64 .x25) (s1.readReg64 .x12) (s1.readReg64 .x11) (s1.readReg64 .x10)
         (s1.readReg64 .x15) (s1.readReg64 .x28) (s1.readReg64 .x7) (s1.readReg64 .x0)
         (s1.readReg64 .x6) (s1.readReg64 .x30) (s1.readReg64 .x21) (s1.readReg64 .x9)
         (s1.readReg64 .x5) (s1.readReg64 .x4) (s1.readReg64 .x13) (s1.readReg64 .x14) ∗
       epilogueRecvOutPartB488 outA w424 (s1.readReg64 .x23) (s1.readReg64 .x27) w440
         w264 w344 w392 w272 w360 w400 w464 w304 w328 w280 w320 (s1.readReg64 .x3)
         w312 (s1.readReg64 .x24) w416 (s1.readReg64 .x17) w472 (s1.readReg64 .x26)
         w448 (s1.readReg64 .x22) w480 (s1.readReg64 .x16) w488 (s1.readReg64 .x2) w248 (s1.readReg64 .x20) ∗
       memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
      (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
       statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
      (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

theorem subroutine_ok_statesRecvVariantSpec_of_sepWP
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64} {ext : String → Option (State → State)}
    (self : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hwp : ∀ (outA selfA msgA : BitVec 64) (s0 : State),
      s0.pc = (tripleRatchetProgAtExt b ext).fnAddr statesRecvName → s0.status = .Running →
      (s0.sp &&& 15#64 == 0#64) = true → b &&& 0xfff#64 = 0#64 →
      s0.readReg64 .x0 = outA → s0.readReg64 .x1 = selfA → s0.readReg64 .x2 = msgA →
      statesRecvPreInv self →
      SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s0
        (stackAt s0.sp statesRecvStackX ∗
         (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
          messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool))
        (fun sf Pf =>
          (Pf ⊢ resultV1RecvAt A (F := F) outA (self.recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
            statesRecvRoAt b ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName) (statesRecvVariantSpec A F K b self msg) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨outA, selfA, msgA⟩ R s0 hpc0 hrun0 hpre hsp0_align
  simp only [statesRecvVariantSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hb, hx0, hx1, hx2, hinv⟩, hmem⟩
  refine ⟨stackAt s0.sp statesRecvStackX ∗ (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA self ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool), R, Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem, ?_⟩
  dsimp only [statesRecvVariantSpec]
  refine SepWPp.of_sepWP (SepWP.mono (hwp outA selfA msgA s0 hpc0 hrun0 hsp0_align hb hx0 hx1 hx2 hinv) ?_)
  intro sf Pf hpc_f hrun_f ⟨hPf, hsp_f, hcs_f, htr_f⟩
  refine SepWPp.done hpc_f hrun_f ⟨fun hsat => ?_, hsp_f, hcs_f⟩
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right htr_f (Entails.refl _)))
    (Satisfies.mono (sepConj_mono_left hPf) hsat)

/-- Per-variant specification proof for `States.keysUnsampled st` (`tag = 2#64`). -/
theorem states_recv_keysUnsampled_ok_ext
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (b : BitVec 64) (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr statesRecvName)
      (statesRecvVariantSpec A F K b (.keysUnsampled st) msg) := by
  refine subroutine_ok_statesRecvVariantSpec_of_sepWP (.keysUnsampled st) msg ?_
  intro outA selfA msgA s0 hpc0 hrun0 hsp0_align hb hx0 hx1 hx2 _
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue (b := b) (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool) hsp0_align hpc0 hrun0
  refine seq_clean hpro ?_
  intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; rw [chunkedStatesAt_keysUnsampled_unfold]
  have hdisp := states_recv_dispatch (b := b) (ext := ext) hb s1 (s0.sp - 4240#64) selfA 2#64
    (authenticatorAt A (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
     memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (Or.inr (Or.inr (Or.inl rfl))) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, hx0_2, hx1_2, hx2_2, _, _, _, hx19_2, _, hx24_2, _, hx29_2, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2; rw [hx29_1] at hx29_2
  have htr20 : TraceCalleeSaved s2 s0 := htr2.trans htr1
  have hpre2 :
      (selfA ↦₆₄ 2#64) ∗ statesRecvRoAt b ∗
      (authenticatorAt A (selfA + 8#64) st.uc.auth ∗ ((selfA + 56#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (selfA + 64#64) 864 ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0) ⊢
      (∃∗ v48 : BitVec 64, (((s0.sp - 4240#64) + 48#64) ↦₆₄ v48)) ∗
      (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.keysUnsampled st) ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoAt b ∗ A.pool ∗
       stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 48 ∗
       memRegion ((s0.sp - 4240#64) + 56#64) 4088 ∗ statesRecvSavedCells s0) := by
    rw [chunkedStatesAt_keysUnsampled_unfold, memRegion_4144_split_cell48 (s0.sp - 4240#64)]; exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_; rw [sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro v48
  by_cases hgt : msg.epoch > st.uc.epoch
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (states_recv_keysUnsampled_err_96 hA s0 s2 (s0.sp - 4240#64) outA selfA msgA v48 st msg
        hgt rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx29_2 hx19_2 hx1_2 hx24_2 htr20)
  · exact SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (states_recv_keysUnsampled_ok_96 hA s0 s2 (s0.sp - 4240#64) outA selfA msgA v48 st msg
        hgt rfl hsp0_align hfsp_align hpc2 hrun2 hsp2 hx19_2 hx1_2 hx24_2 htr20)

end CryptoVerification.SpqrV1.States.Recv
