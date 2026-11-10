/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Version Dispatch Exits & `Ordering::Equal` Transition

Version-dispatch cleanup/error exits (`+752`, `+892`, `+912`, `+936`, `+1028`, `+2540`),
`Ordering::Equal` transition (`+792..+820 -> +1532`), and `SepWPpI.call_inImage` for
`spqr::recv` (`0x5462c`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Split `memRegion r 48` exposing `(r + 8#64) ↦₈ b8` and `memRegion (r + 9#64) 7` for `strb
    w8, [x19, #0x8]`. -/
theorem ret_48_split_byte8 (r : BitVec 64) :
    memRegion r 48 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ b8 : BitVec 8, ∃∗ r2 : BitVec 64, ∃∗ r3 : BitVec 64,
        (r ↦₆₄ r0) ∗ ((r + 8#64) ↦₈ b8) ∗ memRegion (r + 9#64) 7 ∗
        ((r + 16#64) ↦₆₄ r2) ∗ ((r + 24#64) ↦₆₄ r3) ∗ memRegion (r + 32#64) 16 := by
  rw [ret_48_split r]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro r3
  apply Entails.sepExists_elim; intro r2
  apply Entails.sepExists_elim; intro r1
  apply Entails.sepExists_elim; intro r0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (ret8_expose_byte r r1))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro b8
  refine Entails.sepExists_right r0 (Entails.sepExists_right b8
    (Entails.sepExists_right r2 (Entails.sepExists_right r3 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem cap_ne_zero_one_sle_true {w0 : BitVec 64} (hcap_lt : w0.toNat < 2 ^ 63)
    (hc0 : ¬(w0 == 0#64) = true) :
    (1#64).sle w0 = true := by
  have hne : w0.toNat ≠ 0 := by
    intro h0; apply hc0; rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h0
  unfold BitVec.sle BitVec.toInt
  simp only [Nat.reducePow, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reduceMul, ↓reduceIte,
    decide_eq_true_eq]
  split <;> omega

theorem vnHeader_sub4992_entails_memRegion_48 (sp0 w0 w1 : BitVec 64) :
    ((sp0 - 4992#64) ↦₆₄ w0) ∗ ((sp0 - 4984#64) ↦₆₄ w1) ∗ memRegion (sp0 - 4976#64) 32 ⊢
      memRegion (sp0 - 4992#64) 48 := by
  have h8 : (sp0 - 4992#64) + 8#64 = sp0 - 4984#64 := bv_sub_add_lit sp0 4992 8
  have h16 : (sp0 - 4992#64) + 16#64 = sp0 - 4976#64 := bv_sub_add_lit sp0 4992 16
  rw [← h8, ← h16]
  exact vnHeader_entails_memRegion_48 (sp0 - 4992#64) w0 w1

/-- Deallocate non-empty `vn.authKey` at `+936 .. +948` and continue to `step_drop_pre_952`. -/
theorem step_drop_vn_936 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      memRegion (s0.sp - 4976#64) 32 ∗
      A.live w1 w0.toNat 1 ∗
      memRegion w1 w0.toNat ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 936 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 952#64)
    (P_mid := spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
    ?_ ?_
  · refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
    wp_steps; wp_apply
    have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hx26_1⟩
    exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 s1 _ R post hpost
      hs0_align (by rw [spqrRecvEntry_eq, hentry]; exact hpc1) hrun1 hsp1 htr1 hx26_1 rfl

/-- `Err(VersionMismatch)` exit at `+892 .. +908` (`-> +952`): stores `-1` and `7`
    (`Error::VersionMismatch`) at `ret` (`x19`) and continues to `step_drop_pre_952`. -/
theorem step_err_versionMismatch_892 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 892#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 892 20
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  wp_steps 5
  have hfold := recv_err_byte_foldX A ret r2 r3 7#8 false (by decide)
  rw [← herr] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
    hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl)

/-- `Err(MinVersion)` exit at `+752 .. +776` (`-> +936 / +952`): stores `-1` and `8`
    (`Error::MinVersion`) at `ret` (`x19`), drops `pre_pb.versionNegotiation` if `w0 >= 1`, and
    continues to `step_drop_pre_952`. -/
theorem step_err_minVersion_752 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 752#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 752 28
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  have hfold := recv_err_byte_foldX A ret r2 r3 8#8 false (by decide)
  rw [← herr] at hfold
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    wp_steps 7
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
      hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl)
  | some vn =>
    have hvn_dealloc :
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
          vecCapPtrDealloc A w0 w1 := by
      have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
      have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
      rw [← h8, ← h16]
      exact vnTail_some_entails_dealloc A (s0.sp - 4992#64) w0 w1 vn
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 7
      refine SepWP.fold hfold (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
        hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl)
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      wp_steps 6
      refine SepWP.fold hfold (by sep_focus) ?_
      exact step_drop_vn_936 b A M ext hb hdealloc st msg ret pre_pb w0 w1 w26 hw26 s0 _ _ R post hpost
        hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl)

/-- `Ok((Vec::new(), None))` exit at `+912 .. +932` (`-> +936 / +952`): stores `Ok(([], None))`
    (`(0, 1, 0, -1)`) at `ret` (`x19`), drops `pre_pb.versionNegotiation` if `w0 >= 1`, and
    continues to `step_drop_pre_952`. -/
theorem step_ok_none_912 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hok : M.recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 912#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName] at hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 912 24
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  rw [ret_48_split ret]
  wp_pull_exists; rename_i r3 r2 r1 r0
  have hfold := recv_ok_empty_foldX A ret
  rw [← hok] at hfold
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0
    subst hw0
    have hslt : BitVec.slt noneCap 1#64 = true := rfl
    wp_steps 6
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
      hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl)
  | some vn =>
    have hvn_dealloc :
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ⊢
        ⌜w0.toNat < 2 ^ 63⌝ ∗
          ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
          vecCapPtrDealloc A w0 w1 := by
      have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
      have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
      rw [← h8, ← h16]
      exact vnTail_some_entails_dealloc A (s0.sp - 4992#64) w0 w1 vn
    refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 6
      refine SepWP.fold hfold (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      exact step_drop_pre_952 b A M ext hb hdealloc st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
        hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl)
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      wp_steps 6
      refine SepWP.fold hfold (by sep_focus) ?_
      exact step_drop_vn_936 b A M ext hb hdealloc st msg ret pre_pb w0 w1 w26 hw26 s0 _ _ R post hpost
        hs0_align (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl)

/-- Drop `optProtoInnerStateAt` at `s0.sp - 4864#64` (`sp + 0x80`) via `+1028 .. +1036` and
    return via `step_epilogue` (`+1040 .. +1072`). -/
theorem step_drop_inner_1028 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (optSt : Option V1State.InnerState)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4864#64) optSt ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hinner_raw := spqrRecv_dropOptProtoInnerState_ok hdealloc
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, Drop.dropOptProtoInnerStateSpec,
    Drop.optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hinner_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 1028 16
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  have hjoin352 : memRegion (s0.sp - 4992#64) 128 ∗ memRegion (s0.sp - 4864#64) 224 ⊢
      memRegion (s0.sp - 4992#64) 352 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 128) (k := 224)
        (b' := s0.sp - 4864#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine seq_clean (mid := entry + 1040#64)
    (P_mid := spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
    ?_ ?_
  · unfold spqrRecvRoAt Prost.MessageMerge.v1StateJumpTablesAt
    wp_steps
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide))) (by sep_focus) ?_
    wp_call hinner_raw ⟨s0.sp - 4864#64, optSt⟩
    have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
    refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1⟩
    exact step_epilogue b A M ext st msg ret s0 s1 _ R post hpost
      (by rw [spqrRecvEntry_eq, hentry]; exact hpc1)
      hrun1 hsp1 hs0_align htr1 rfl

/-- Drop `pre_pb.versionNegotiation` (`some vn` at `s0.sp - 4992#64`, capacity `w0` in `x20`) at
    `+2540 .. +2564` and jump to `+1028` (`step_drop_inner_1028`) to drop `pre_pb.inner` (`some
    (.v1 pb)`) and return. -/
theorem step_drop_pre_2540 (b : BitVec 64) (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPost0 A b M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 2540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ∗
      memRegion (s0.sp - 4944#64) 80 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) (some (.v1 pb)) ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_raw := spqrRecv_dealloc_ok hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hvn_dealloc :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) (some vn) ⊢
      ⌜w0.toNat < 2 ^ 63⌝ ∗
        ((s0.sp - 4992#64) ↦₆₄ w0) ∗ ((s0.sp - 4984#64) ↦₆₄ w1) ∗ memRegion (s0.sp - 4976#64) 32 ∗
        vecCapPtrDealloc A w0 w1 := by
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    rw [← h8, ← h16]
    exact vnTail_some_entails_dealloc A (s0.sp - 4992#64) w0 w1 vn
  have hjoin128 : memRegion (s0.sp - 4992#64) 48 ∗ memRegion (s0.sp - 4944#64) 80 ⊢
      memRegion (s0.sp - 4992#64) 128 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 48) (k := 80)
        (b' := s0.sp - 4944#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, Drop.optProtoPqRatchetInnerAt,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 2540 28
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 1028#64)
    (P_mid := spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4864#64) pb.innerState ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
    ?_ ?_
  · refine SepWP.focus_weaken hvn_dealloc (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      refine align_pre (by ac_rfl) ?_; wp_done
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
      wp_steps; wp_apply
      have hsp_eq : stackAt s.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp]
      refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
      refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      wp_steps
      refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1⟩
    exact step_drop_inner_1028 b A M ext hb hdealloc st msg ret pb.innerState s0 s1 _ R post hpost
      hs0_align (by rw [spqrRecvEntry_eq, hentry]; exact hpc1) hrun1 hsp1 htr1 rfl

/-! ## `Ordering::Equal` Transition (`+792 .. +820 -> +1532`) -/

/-- Pinned 352-byte `PqRatchetState` layout keeping the first two words `w0, w1` of
    `versionNegotiation` explicit. -/
def pinnedPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc) (w0 w1 : BitVec 64)
    (a : BitVec 64) (st : PqRatchetState) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
  optVersionNegotiationPBTailAt A w0 w1 (a + 16#64) st.versionNegotiation ∗
  optChainPBAt A (a + 48#64) st.chain ∗
  DecodeState.optProtoPqRatchetInnerAt H_inner A (a + 128#64) st.inner

def relocPinnedPqRatchetStateAt (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (w0 w1 : BitVec 64) (st : PqRatchetState) :
    Σ' H, Relocatable (fun a => pinnedPqRatchetStateAt H_inner A w0 w1 a st) 352 H :=
  let h1 := reloc_append 16 8#64 (reloc_pointsTo64 w0) (reloc_pointsTo64 w1) rfl rfl
  let h2 := reloc_append 352 16#64 h1 (relocProtoPqRatchetStateTailAt H_inner A w0 w1 st).2 rfl rfl
  ⟨_, reloc_congr h2 (fun a => by
    unfold pinnedPqRatchetStateAt protoPqRatchetStateTailAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])⟩

theorem optProtoPqRatchetInnerAt_eq_drop {H_inner : V1InnerHeapPred} {A : RustAlloc}
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (a : BitVec 64) (opt : Option PqRatchetState.Inner) :
    DecodeState.optProtoPqRatchetInnerAt H_inner A a opt = Drop.optProtoPqRatchetInnerAt A a opt := by
  cases opt with
  | none => rfl
  | some inn =>
    cases inn with
    | v1 v1 => exact h_inner_eq a v1.innerState

/-- Continuation contract at `+1532` for the V1 ratchet path (`Ordering::Equal`). -/
def V1RatchetTail (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (post : State → SepProp → Prop) : Prop :=
  ∀ (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64) (s : State) (P : SepProp),
    msgPreamble msg.bytes = .ok pre →
    MsgRemValid msg remPtr pre.remaining →
    Proto.spqrDecodeState st.bytes = .ok pre_pb →
    pre_pb.inner = some (.v1 pb) →
    w0 ≠ DecodeState.none2Cap →
    pre.version = 1#8 →
    (∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8)) →
    s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 1532#64 →
    s.status = .Running →
    s.sp = s0.sp - 4992#64 →
    TraceVRegs s s0 →
    s.readReg64 .x19 = ret →
    s.readReg64 .x20 = w0 →
    s.readReg64 .x21 = pre.index.zeroExtend 64 →
    s.readReg64 .x22 = pre.epoch →
    s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
    s.readReg64 .x24 = remPtr →
    s.readReg64 .x26 = 0#64 →
    s.readReg64 .x27 = s0.sp - 3056#64 →
    s.readReg64 .x28 = s0.sp - 4288#64 →
    s.readReg64 .x29 = s0.sp - 96#64 →
    P = (spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
      ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState ∗
      memRegion (s0.sp - 4288#64) 4192 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post

/-- `Ordering::Equal` transition at `+792 .. +820` (`-> +1532`): copies `pre_pb` (`352`B) from
    `sp` (`s0.sp - 4992#64`) to `sp + 0x160` (`s0.sp - 4640#64`), sets `w26 = 0`, checks
    `state_pb.inner != None` (`cmn x8, #3; b.ne +1532`), and continues to `V1RatchetTail`. -/
theorem step_equal_792 (H_inner : V1InnerHeapPred) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (remPtr : BitVec 64) (pre_pb : PqRatchetState) (pb : V1State)
    (w0 w1 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hvalid : MsgRemValid msg remPtr pre.remaining)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hw0_ne : w0 ≠ DecodeState.none2Cap)
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (htail : V1RatchetTail b A ext st msg ret s0 post)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrRecvName + 792#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = pre.index.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = pre.epoch)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length)
    (hx24 : s.readReg64 .x24 = remPtr)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hx28 : s.readReg64 .x28 = s0.sp - 4288#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt b ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
      ((s0.sp - 4984#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := spqrRecv_memcpy_ok hA spqrRecvCalleeStackX
  simp only [sessionMemcpySpec] at hmemcpy
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  have hto :
      ((s0.sp - 4992#64) ↦₆₄ w0) ∗
        ((s0.sp - 4984#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4976#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ⊢
      ∃∗ bs352 : List (BitVec 8),
        ⌜bs352.length = 352⌝ ∗
        ((s0.sp - 4992#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.to_bytes (s0.sp - 4992#64)
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4992#64) + 8#64 = s0.sp - 4984#64 := bv_sub_add_lit s0.sp 4992 8
    have h16 : (s0.sp - 4992#64) + 16#64 = s0.sp - 4976#64 := bv_sub_add_lit s0.sp 4992 16
    have h48 : (s0.sp - 4992#64) + 48#64 = s0.sp - 4944#64 := bv_sub_add_lit s0.sp 4992 48
    have h128 : (s0.sp - 4992#64) + 128#64 = s0.sp - 4864#64 := bv_sub_add_lit s0.sp 4992 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsplit_4544 :
      memRegion (s0.sp - 4640#64) 4544 =
        memRegion (s0.sp - 4640#64) 352 ∗ memRegion (s0.sp - 4288#64) 4192 :=
    ProofLib.memRegion_split' (b := s0.sp - 4640#64) (n := 352) (k := 4192)
      (b' := s0.sp - 4288#64) rfl (by bv_omega) (by decide)
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hmemcpy hpc ⊢
  have hentry : spqrRecvEntry b ext =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  spqr_recv_fetches_range b (Rust.withPanics ext) 792 32
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken hto (by sep_focus) ?_
  wp_pull_exists; rename_i bs352
  wp_focus_pure; intro hlen352
  rw [hsplit_4544]
  have hof :
      ((s0.sp - 4640#64) ↦ₛ bs352) ∗
        (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).1 bs352 ⊢
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗
        ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        optChainPBAt A (s0.sp - 4592#64) pre_pb.chain ∗
        Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner := by
    have h := (relocPinnedPqRatchetStateAt H_inner A w0 w1 pre_pb).2.of_bytes (s0.sp - 4640#64) bs352 hlen352
    unfold pinnedPqRatchetStateAt at h
    rw [optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at h
    have h8 : (s0.sp - 4640#64) + 8#64 = s0.sp - 4632#64 := bv_sub_add_lit s0.sp 4640 8
    have h16 : (s0.sp - 4640#64) + 16#64 = s0.sp - 4624#64 := bv_sub_add_lit s0.sp 4640 16
    have h48 : (s0.sp - 4640#64) + 48#64 = s0.sp - 4592#64 := bv_sub_add_lit s0.sp 4640 48
    have h128 : (s0.sp - 4640#64) + 128#64 = s0.sp - 4512#64 := bv_sub_add_lit s0.sp 4640 128
    rw [h8, h16, h48, h128] at h
    exact h
  have hsrc_mem : ((s0.sp - 4992#64) ↦ₛ bs352) ⊢ memRegion (s0.sp - 4992#64) 352 := by
    rw [← hlen352]
    exact ProofLib.pointsToBytes_entails_memRegion (s0.sp - 4992#64) bs352
  wp_steps 4
  have hdst_mem : memRegion (s0.sp - 4640#64) 352 = memRegion (s0.sp - 4640#64) bs352.length := by
    rw [hlen352]
  have hlen_eq : (352#64 : BitVec 64).toNat = bs352.length := hlen352.symm
  have hsp_eq : stackAt s.sp spqrRecvCalleeStackX = stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX := by rw [hsp]
  rw [hdst_mem]
  wp_call hmemcpy ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
  rw [hsp_eq]
  refine SepWP.focus_weaken hsrc_mem (by sep_focus) ?_
  refine SepWP.focus_weaken hof (by sep_focus) ?_
  refine SepWP.focus_weaken
    (optProtoPqRatchetInnerAt_expose_word A (s0.sp - 4512#64) pre_pb.inner) (by sep_focus) ?_
  wp_pull_exists; rename_i w8 P_inner
  wp_focus_pure; intro hw8
  wp_focus_pure; intro hunexp
  have hw8_bne3 : (w8 + 3#64 != 0#64) = true := by
    rw [hinner] at hw8
    dsimp [InnerWordInv] at hw8
    simp [bne, hw8]
  wp_steps 4
  refine SepWP.focus_weaken hunexp (by sep_focus) ?_
  have hinner_eq : Drop.optProtoPqRatchetInnerAt A (s0.sp - 4512#64) pre_pb.inner =
      Drop.optProtoInnerStateAt A (s0.sp - 4512#64) pb.innerState := by
    rw [hinner]; rfl
  rw [hinner_eq]
  exact htail pre remPtr pre_pb pb w0 w1 _ _ hpre hvalid hdec hinner hw0_ne hmv hmin
    (by rw [spqrRecvEntry_eq, hentry]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## Panic Postcondition & Generic `.inImage` Call Wrapper (`SepWPpI.call_inImage`) -/

theorem allocFailedIn_of_prefix {s0 s sm : State}
    (hpre : s0.trace <+: s.trace)
    (h : allocFailedIn s sm ∧ s.trace <+: sm.trace) :
    allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
  have hsub := hpre.trans h.2
  rcases hpre with ⟨t1, ht1⟩
  rcases h with ⟨hmem, t2, ht2⟩
  unfold allocFailedIn at hmem ⊢
  refine ⟨?_, hsub⟩
  have hdrop : sm.trace.drop s.trace.length = t2 := by
    rw [← ht2, List.drop_left]
  have hdrop0 : sm.trace.drop s0.trace.length = t1 ++ t2 := by
    have hsm : sm.trace = s0.trace ++ (t1 ++ t2) := by
      rw [← List.append_assoc, ht1, ht2]
    rw [hsm, List.drop_left]
  rw [hdrop0]
  rw [hdrop] at hmem
  exact List.mem_append_right t1 hmem

theorem panic_prefix_trans {M : SpqrRecvModel} {st msg : VecArg} {s0 s sm : State}
    (hpre : s0.trace <+: s.trace)
    (h : (allocFailedIn s sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace) :
    (allocFailedIn s0 sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sm.trace := by
  rcases h with ⟨haf | hpan, hsub⟩
  · exact ⟨Or.inl (allocFailedIn_of_prefix hpre ⟨haf, hsub⟩).1, hpre.trans hsub⟩
  · exact ⟨Or.inr hpan, hpre.trans hsub⟩

theorem onPanic_of_allocFailed {M : SpqrRecvModel} {st msg : VecArg} {s sm : State} :
    (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap : SepProp) ⊢
      ⌜(allocFailedIn s sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap := by
  apply Entails.pure_left; rintro ⟨haf, hsub⟩
  exact Entails.pure_right ⟨Or.inl haf, hsub⟩ (Entails.refl _)

theorem SepWPpI.call_inImage {α : Type} {img : Obj.Image} {prog : Program}
    {M : SpqrRecvModel} {st msg : VecArg}
    {ret entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (x : α) {s0 s : State} {P F R : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (halign : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s0.trace <+: s.trace)
    (hpan : ∀ sm, spec.onPanic x s sm ⊢
      ⌜(allocFailedIn s sm ∨ M.recvPanics st.bytes msg.bytes) ∧ s.trace <+: sm.trace⌝ ∗ anyHeap)
    (hexit : ∀ code sm, spec.onExit x code s sm = ⌜False⌝)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpost : ∀ sm,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = s.sp →
      CalleeSavedPreserved s sm →
      SepWPpI img prog ret sm (spec.post x s sm ∗ F) Q (spqrRecvPanicPost M st msg s0 R))
    (hoom : ∀ sm, spec.onOom x s sm = ⌜False⌝ := by intros; rfl) :
    SepWPpI img prog ret s P Q (spqrRecvPanicPost M st msg s0 R) := by
  intro hinv
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hinv.1 hinv.2 hpc hrun halign hlr
    ?_ ?_ ?_ ?_ ?_
  · intro R' hm
    have hm1 := Satisfies.mono (sepConj_mono_left hpre) hm
    change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗ (F ∗ R')
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, by rw [← sepConj_assoc]; exact hm1⟩
  · intro sm code R' _ hpost_m
    change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost_m
    rw [hexit code sm] at hpost_m
    exact not_satisfies_false_sepConj hpost_m
  · intro sm _ _ hm''
    change sm.mem ⊨ (spec.onPanic x s sm ∗ F) ∗ R at hm''
    have hm_pan := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (hpan sm))) hm''
    exact allowPanic_frame (panic_prefix_trans htr) hm_pan
  · intro sm hpcm hrunm hspm hcsm hfz_m hsym_m
    exact hpost sm hpcm hrunm hspm hcsm ⟨hfz_m, hsym_m⟩
  · intro sm R' _ hpost_m
    change sm.mem ⊨ spec.onOom x s sm ∗ (F ∗ R') at hpost_m
    rw [hoom sm] at hpost_m
    exact (not_satisfies_false_sepConj hpost_m).elim

end CryptoVerification.SpqrV1.Top.Recv
