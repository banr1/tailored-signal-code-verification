/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1Placed
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Version Dispatch Exits & `Ordering::Equal` Transition for `spqr::recv`

Relocatable version-dispatch cleanup exits, `Ordering::Equal` transition (`+792..+820 -> +1532`),
and `withLsCodeRoLoaded` call wrapper (`SepWPpLS.call_lscro`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

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
open CryptoVerification.SpqrV1.Top.Recv.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Version Dispatch Exits (`+752`, `+892`, `+912`, `+936`, `+1028`, `+2540`) -/

/-- Relocatable deallocate non-empty `vn.authKey` at `+936 .. +948` and continue to
    `step_drop_pre_952_placed`. -/
theorem step_drop_vn_936_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 936#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
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
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_raw := hC.dealloc_ok
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_329).base + 952#64)
    (P_mid := spqrRecvRoPlacedAt ∗
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
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hx26_1⟩
    exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 s1 _ R post hpost
      hs0_align hpc1 hrun1 hsp1 htr1 hx26_1 rfl hcl1

/-- Relocatable `Err(VersionMismatch)` exit at `+892 .. +908` (`-> +952`): stores `-1` and `7`
    (`Error::VersionMismatch`) at `ret` (`x19`) and continues to `step_drop_pre_952_placed`. -/
theorem step_err_versionMismatch_892_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 892#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 48 ∗
      optChainPBAt A (s0.sp - 4944#64) pre_pb.chain ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
  apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 952#64)
  refine SepWP.focus_weaken (ret_48_split_byte8 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 b8 r2 r3
  wp_steps 5
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcl1
  have hfold := recv_err_byte_foldX A ret r2 r3 7#8 false (by decide)
  rw [← herr] at hfold
  refine SepWP.fold hfold (by sep_focus) ?_
  exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
    hs0_align (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]; ac_rfl) hcl1

/-- Relocatable `Err(MinVersion)` exit at `+752 .. +776` (`-> +936 / +952`): stores `-1` and `8`
    (`Error::MinVersion`) at `ret` (`x19`), drops `pre_pb.versionNegotiation` if `w0 >= 1`, and
    continues to `step_drop_pre_952_placed`. -/
theorem step_err_minVersion_752_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (herr : M.recv st.bytes msg.bytes = .error false)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 752#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
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
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
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
    apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 952#64)
    wp_steps 7
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
      hs0_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl) hcl1
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
      apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 952#64)
      wp_steps 7
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine SepWP.fold hfold (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
        hs0_align (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl) hcl1
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 936#64)
      wp_steps 6
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine SepWP.fold hfold (by sep_focus) ?_
      exact step_drop_vn_936_placed A M ext hC st msg ret pre_pb w0 w1 w26 hw26 s0 _ _ R post hpost
        hs0_align (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl) hcl1

/-- Relocatable `Ok((Vec::new(), None))` exit at `+912 .. +932` (`-> +936 / +952`): stores
    `Ok(([], None))` (`(0, 1, 0, -1)`) at `ret` (`x19`), drops `pre_pb.versionNegotiation` if
    `w0 >= 1`, and continues to `step_drop_pre_952_placed`. -/
theorem step_ok_none_912_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w0 w1 w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (hok : M.recv st.bytes msg.bytes = .ok ([], none))
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 912#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = w0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
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
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry] at hpc ⊢
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
    apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 952#64)
    wp_steps 6
    apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine SepWP.fold hfold (by sep_focus) ?_
    refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
      hs0_align (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]; ac_rfl) hcl1
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
      apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 952#64)
      wp_steps 6
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine SepWP.fold hfold (by sep_focus) ?_
      refine SepWP.focus_weaken (vnHeader_sub4992_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      exact step_drop_pre_952_placed A M ext hC st msg ret pre_pb w26 hw26 s0 _ _ R post hpost
        hs0_align (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl) hcl1
    · have hslt := Drop.cap_ne_zero_slt_one_false hcap_lt hc0
      have hlt_false := Drop.cap_ne_zero_lt_one_false hcap_lt hc0
      apply sepWP_seq_lscl hcl (mid := (blkPl_329).base + 936#64)
      wp_steps 6
      apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine SepWP.fold hfold (by sep_focus) ?_
      exact step_drop_vn_936_placed A M ext hC st msg ret pre_pb w0 w1 w26 hw26 s0 _ _ R post hpost
        hs0_align (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]; ac_rfl) hcl1

/-- Relocatable drop `optProtoInnerStateAt` at `s0.sp - 4864#64` (`sp + 0x80`) via `+1028 ..
    +1036` and return via `step_epilogue_placed` (`+1040 .. +1072`). -/
theorem step_drop_inner_1028_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (optSt : Option V1State.InnerState)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 1028#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 4864#64) optSt ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hinner_raw := hC.dropOptProtoInnerState_ok
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, Drop.dropOptProtoInnerStatePlacedSpec,
    Drop.optProtoInnerStateSize, BitVec.ofNat_eq_ofNat] at hinner_raw hpc ⊢
  have hjoin352 : memRegion (s0.sp - 4992#64) 128 ∗ memRegion (s0.sp - 4864#64) 224 ⊢
      memRegion (s0.sp - 4992#64) 352 := by
    rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 128) (k := 224)
        (b' := s0.sp - 4864#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine seq_clean (mid := (blkPl_329).base + 1040#64)
    (P_mid := spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
    ?_ ?_
  · unfold spqrRecvRoPlacedAt Prost.MessageMerge.v1StateJumpTablesPlacedAt
    wp_steps
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide))) (by sep_focus) ?_
    wp_call (subroutine_ok_withMemEq_of_lscl hinner_raw hcl) ⟨s0.sp - 4864#64, optSt⟩
    have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
    refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
    refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm) (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
    refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
    refine align_pre (by ac_rfl) ?_; wp_done
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1⟩
    exact step_epilogue_placed A M ext st msg ret s0 s1 _ R post hpost
      hpc1 hrun1 hsp1 hs0_align htr1 rfl

/-- Relocatable drop `pre_pb.versionNegotiation` (`some vn` at `s0.sp - 4992#64`, capacity `w0`
    in `x20`) at `+2540 .. +2564` and jump to `+1028` (`step_drop_inner_1028_placed`). -/
theorem step_drop_pre_2540_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (vn : VersionNegotiationPB) (pb : V1State) (w0 w1 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2540#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx20 : s.readReg64 .x20 = w0)
    (hP : P =
      spqrRecvRoPlacedAt ∗
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
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_raw := hC.dealloc_ok
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
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, Drop.optProtoPqRatchetInnerAt,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_329).base + 1028#64)
    (P_mid := spqrRecvRoPlacedAt ∗
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
  · intro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1⟩
    exact step_drop_inner_1028_placed A M ext hC st msg ret pb.innerState s0 s1 _ R post hpost
      hs0_align hpc1 hrun1 hsp1 htr1 rfl hcl1

/-! ## 2. Relocatable `Ordering::Equal` Transition (`+792 .. +820 -> +1532`) -/

/-- Relocatable continuation contract at `+1532` for the V1 ratchet path (`Ordering::Equal`). -/
def V1RatchetPlacedTail (A : RustAlloc)
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
    s.pc = spqrRecvPlacedEntry + 1532#64 →
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
    P = (spqrRecvRoPlacedAt ∗
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
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post

/-- Relocatable `Ordering::Equal` transition at `+792 .. +820` (`-> +1532`): copies `pre_pb`
    (`352`B) from `sp` (`s0.sp - 4992#64`) to `sp + 0x160` (`s0.sp - 4640#64`), sets `w26 = 0`,
    checks `state_pb.inner != None` (`cmn x8, #3; b.ne +1532`), and continues to
    `V1RatchetPlacedTail`. -/
theorem step_equal_792_placed {F : ShaCompress} {K : MlKem}
    (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
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
    (htail : V1RatchetPlacedTail A ext st msg ret s0 post)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 792#64)
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
      spqrRecvRoPlacedAt ∗
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
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hmemcpy := hC.memcpy_ok
  simp only [framelessMemcpySpec] at hmemcpy
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
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hmemcpy hpc ⊢
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
  rw [hdst_mem]
  wp_call hmemcpy ⟨s0.sp - 4640#64, s0.sp - 4992#64, bs352⟩
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
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by ac_rfl)

/-! ## 3. Generic `withLsCodeRoLoaded` Call Wrapper (`SepWPpLS.call_lscro`) -/

theorem SepWPpLS.call_lscro {α : Type} {prog : Program}
    {M : SpqrRecvModel} {st msg : VecArg}
    {ret entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
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
      SepWPpLS prog ret sm (spec.post x s sm ∗ F) Q (spqrRecvPanicPost M st msg s0 R))
    (hoom : ∀ sm, spec.onOom x s sm = ⌜False⌝ := by intros; rfl) :
    SepWPpLS prog ret s P Q (spqrRecvPanicPost M st msg s0 R) := by
  intro hcrl R' hm hL
  have hm1 := Satisfies.mono (sepConj_mono_left hpre) hm
  have hpre_lscro : s.mem ⊨ (withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R') := by
    change s.mem ⊨ (spec.pre x s ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ (F ∗ R')
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrl, by rw [← sepConj_assoc]; exact hm1⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre_lscro halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost_m⟩ | ⟨hpan_st, hpost_m⟩ | ⟨code, _, hpost_m⟩ | ⟨_, hpost_m⟩
  · change sm.mem ⊨ spec.post x s sm ∗ (F ∗ R') at hpost_m
    rw [← sepConj_assoc] at hpost_m
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hpost sm hpcm hrunm hspm hcsm (hsteps.lsCodeRoLoaded hcrl) R' hpost_m (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ spec.onPanic x s sm ∗ (F ∗ R') at hpost_m
    have hpost_pan := Satisfies.mono (sepConj_mono_left (hpan sm)) hpost_m
    rw [← sepConj_assoc] at hpost_pan
    refine ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost_pan, ?_⟩)⟩
    intro hm''
    exact allowPanic_frame (panic_prefix_trans htr) hm''
  · change sm.mem ⊨ spec.onExit x code s sm ∗ (F ∗ R') at hpost_m
    rw [hexit code sm] at hpost_m
    exact (not_satisfies_false_sepConj hpost_m).elim
  · change sm.mem ⊨ spec.onOom x s sm ∗ (F ∗ R') at hpost_m
    rw [hoom sm] at hpost_m
    exact (not_satisfies_false_sepConj hpost_m).elim

end CryptoVerification.SpqrV1.Top.Recv
