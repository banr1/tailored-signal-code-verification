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
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Proof
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Relocatable Prologue & Drop Tail for `spqr::recv`

Relocatable empty-message preamble path, prologue entry (`+0..+312`), and inlined
`drop_glue::<PqRatchetState>` tail (`+952..+1036`) for `spqr::recv` (Block `329`).
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
open CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
  (msgByteFrame msg_expose_byte msg_unexpose_byte
   varint_out_norm list_cons_of_length_pos
   nat_le_of_bv_ule nat_lt_of_not_bv_ule
   hb_ne_of_sxtb_tb hb_eq_of_not_sxtb_tb
   csel_rest1_min_10 rest1_nil_of_ule rest1_cons_of_not_ule
   index_bounds_ne varint_end_of_ge varint_cont_of_lt
   msgHeaderTail msg_expose_hdr msg_unexpose_hdr
   msg_nil_of_len_zero msg_singleton_of_len_one msg_cons_cons_of_len_ge_two)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Empty-Message Preamble Path (`+292 .. +308 -> +312`) -/

/-- Relocatable steps `+292 .. +308` when `msg.bytes = []`, setting `pre = { version := 0#8,
    epoch := 0#64, index := 0#32, remaining := [] }` and `remPtr = 1#64`, and continuing via
    `hok_tail` at `+312`. -/
theorem step_ok_empty_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hmsg_nil : msg.bytes = [])
    (hpc : s.pc = spqrRecvPlacedEntry + 292#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 .x0 = st.v)
    (hx19 : s.readReg64 .x19 = ret)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = spqrRecvPlacedPreambleFrame A st msg ret s0) :
    SepWP (spqrRecvPlacedProg ext) target_pc s P post := by
  have hok : msgPreamble msg.bytes =
      .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } := by
    rw [hmsg_nil]; rfl
  have hvalid : MsgRemValid msg 1#64 [] := Or.inl ⟨rfl, hmsg_nil⟩
  dsimp only [PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hok_tail ⊢
  wp_steps 5
  exact hok_tail
    { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] }
    1#64 _ P hok hvalid
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [hsp, arm64_norm])
    (by simp [htr, arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx19, arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [hx29, arm64_norm])
    hP

/-! ## 2. Prologue + `msg_preamble` Entry (`+0 .. +312`) -/

set_option maxHeartbeats 1600000 in
/-- Relocatable steps from function entry `+0` through the prologue and `msg_preamble` (`+0 ..
    +312`), branching to `herr_tail` at `+276` when `msgPreamble msg.bytes = .error .msgDecode`
    and to `hok_tail` at `+312` when `msgPreamble msg.bytes = .ok pre`. -/
theorem step_prologue_preamble_placed (A : RustAlloc)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret target_pc : BitVec 64)
    (s0 : State) (P : SepProp) (post : State → SepProp → Prop)
    (herr_tail : PreamblePlacedErrTail A ext st msg ret target_pc s0 post)
    (hok_tail : PreamblePlacedOkTail A ext st msg ret target_pc s0 post)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A ∗
      msg.at A ∗
      memRegion ret 48 ∗
      A.pool ∗
      stackAt s0.sp spqrRecvStack) :
    SepWP (spqrRecvPlacedProg ext) target_pc s0 P post := by
  have hok_empty := step_ok_empty_placed A ext st msg ret target_pc s0
  have hep_loop := step_epoch_loop_placed A ext st msg ret target_pc
  subst hP
  dsimp only [PreamblePlacedErrTail, PreamblePlacedOkTail, spqrRecvPlacedProg, spqrRecvPlacedEntry,
    spqrRecvPlacedPreambleFrame, BitVec.ofNat_eq_ofNat] at hpc herr_tail hok_tail hok_empty hep_loop ⊢
  rw [stackAt_spqrRecv_eq_callee_and_frame s0.sp]
  refine SepWP.fold (prologue_frame_split (s0.sp - 4992#64)) (by sep_focus) ?_
  wp_pull_exists
  rename_i s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s30 s29 probe
  have hsp96A : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true := sp_sub_96_aligned s0 hsp_align
  have hsp4192A : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true := sp_sub_4192_aligned s0 hsp_align
  have hsp4992A : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hsp_align
  wp_simp_pre only [bv_sub_add_lit, Nat.reduceSub]
  refine SepWP.fold (msg_expose_hdr A msg) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlen_lt => ?_
  generalize hsp0 : s0.sp = sp0 at hsp96A hsp4192A hsp4992A ⊢
  wp_steps
  subst hsp0
  have hunsplit :
      memRegion (s0.sp - 4992#64) 0x320 ∗
        ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 4184#64) 0xff8 ⊢
      memRegion (s0.sp - 4992#64) 0x1320 := by
    simpa (disch := decide) only [bv_sub_add_lit, Nat.reduceSub, BitVec.ofNat_eq_ofNat] using
      prologue_frame_unsplit (s0.sp - 4992#64) 0#64
  refine SepWP.fold hunsplit (by sep_focus) ?_
  wp_if hlen0
  · refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
    have hmsg_nil : msg.bytes = [] := msg_nil_of_len_zero hlen_lt hlen0
    exact hok_empty _ _ post hok_tail hmsg_nil
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
      (by simp [arm64_norm])
      (by rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]; unfold decodeStateSavedAt; ac_rfl)
  · wp_steps
    wp_if hlen1
    · refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
      obtain ⟨v, hv⟩ := msg_singleton_of_len_one hlen_lt hlen1
      have herr : msgPreamble msg.bytes = .error .msgDecode := by
        rw [hv, msgPreamble_singleton]
      exact herr_tail _ _ herr
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [hx8, arm64_norm])
        (by rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]; unfold decodeStateSavedAt; ac_rfl)
    · wp_steps
      refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
      obtain ⟨version, b₀, rest0', hmsg_eq⟩ := msg_cons_cons_of_len_ge_two hlen_lt hlen0 hlen1
      have hsplit0 : msg.bytes = ([] : List (BitVec 8)) ++ version :: (b₀ :: rest0') := hmsg_eq
      have hoff0 : msg.ptr = msg.ptr + BitVec.ofNat 64 ([] : List (BitVec 8)).length := by
        simp [List.length_nil]
      have hexp0 := msg_expose_byte A msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
      have hunexp0 := msg_unexpose_byte A msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
      clear hoff0 hsplit0
      have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
      refine SepWP.fold hexp0 (by sep_focus) ?_
      wp_steps 4
      refine SepWP.fold hunexp0 (by sep_focus) ?_
      have hlen_eq : msg.bytes.length = 1 + 0 + (b₀ :: rest0').length := by
        rw [← hmsg_symm, List.length_cons]
        omega
      have hpre0 : msgPreamble msg.bytes =
          match LibsignalSpqrV1.decodeVarintLoop 0 0#64 (b₀ :: rest0') with
          | none => .error .msgDecode
          | some (epoch, rest1) =>
            if epoch == 0#64 then .error .msgDecode
            else
              match LibsignalSpqrV1.decodeVarint rest1 with
              | .error e => .error e
              | .ok (index, rest2) =>
                if index.toNat < 2 ^ 32 then
                  .ok { version := version, epoch := epoch, index := index.setWidth 32, remaining := rest2 }
                else .error .msgDecode := by
        rw [← hmsg_symm]; exact msgPreamble_cons_cons version b₀ rest0'
      exact hep_loop version (b₀ :: rest0') s0 post herr_tail hok_tail hlen_lt
        10 0 0#64 [] rest0' b₀ _ _
        (by omega) (by omega) hmsg_symm.symm rfl rfl hpre0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [hx0, arm64_norm]) (by simp [hx8, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by rw [spqrRecvSavedRegs_eq_decodeStateSavedAt s0.sp s0]; unfold decodeStateSavedAt; ac_rfl)

/-! ## 3. Relocatable `PqRatchetState` Drop Tail (`+952 .. +1036`) -/

/-- Relocatable inlined `drop_glue::<PqRatchetState>` tail at `+952 .. +1036` followed by
    `step_epilogue_placed` (`+1040 .. +1072`): drops `pre_pb.chain` at `s0.sp - 4944#64` (`sp +
    0x30`) and `pre_pb.inner` at `s0.sp - 4864#64` (`sp + 0x80`), joins `memRegion (s0.sp -
    4992#64) 352` with `memRegion (s0.sp - 4640#64) 4544` into `memRegion (s0.sp - 4992#64)
    0x1320`, and returns via `step_epilogue_placed`. -/
theorem step_drop_pre_952_placed {H_inner : V1InnerHeapPred} {F : ShaCompress} {K : MlKem}
    (A : RustAlloc) (M : SpqrRecvModel)
    (ext : String → Option (State → State))
    (hC : SpqrRecvPlacedContracts H_inner A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (w26 : BitVec 64)
    (hw26 : InnerWordInv pre_pb.inner w26)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 952#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx26 : s.readReg64 .x26 = w26)
    (hP : P =
      spqrRecvRoPlacedAt ∗
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
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  rcases htr with ⟨htr, hvregs⟩
  have hdealloc_raw := hC.dealloc_ok
  have hslice_raw := hC.dropEpochSlice_ok
  have hinner_raw := hC.dropOptProtoInnerState_ok
  simp only [rustDeallocSpec] at hdealloc_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    dropProtoEpochSliceSpec, CryptoVerification.SpqrV1.Drop.dropOptProtoInnerStatePlacedSpec,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateSize, chainEpochPBSize,
    BitVec.ofNat_eq_ofNat] at hdealloc_raw hslice_raw hinner_raw hpc ⊢
  refine seq_clean_lscl hcl (mid := (blkPl_329).base + 1020#64)
    (P_mid := spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗
      recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
      A.pool ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 128 ∗
      Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
      memRegion (s0.sp - 4640#64) 4544 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
    ?_ ?_
  · have hjoin128 : memRegion (s0.sp - 4992#64) 48 ∗ memRegion (s0.sp - 4944#64) 80 ⊢
        memRegion (s0.sp - 4992#64) 128 := by
      rw [ProofLib.memRegion_split' (b := s0.sp - 4992#64) (n := 48) (k := 80)
          (b' := s0.sp - 4944#64) rfl (by bv_omega) (by decide)]
      exact Entails.refl _
    cases hch : pre_pb.chain with
    | none =>
      dsimp only [optChainPBAt]
      wp_steps
      refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 (s0.sp - 4944#64)) (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      refine align_pre (by ac_rfl) ?_; wp_done
    | some ch =>
      dsimp only [optChainPBAt]
      refine SepWP.focus_weaken (chainPBAt_entails_dealloc A (s0.sp - 4944#64) ch) (by sep_focus) ?_
      wp_pull_exists; rename_i g
      wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
      have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
      have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
        have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le
        omega
      have hne_none := Drop.cap_add_one_beq_zero_false hcap_lt_pow
      have h56 : (s0.sp - 4944#64) + 8#64 = s0.sp - 4936#64 := bv_sub_add_lit s0.sp 4944 8
      have h64 : (s0.sp - 4944#64) + 16#64 = s0.sp - 4928#64 := bv_sub_add_lit s0.sp 4944 16
      have h72 : (s0.sp - 4944#64) + 24#64 = s0.sp - 4920#64 := bv_sub_add_lit s0.sp 4944 24
      have h80 : (s0.sp - 4944#64) + 32#64 = s0.sp - 4912#64 := bv_sub_add_lit s0.sp 4944 32
      have h88 : (s0.sp - 4944#64) + 40#64 = s0.sp - 4904#64 := bv_sub_add_lit s0.sp 4944 40
      refine seq_clean (mid := (blkPl_329).base + 1000#64)
        (P_mid := spqrRecvRoPlacedAt ∗ st.at A ∗ msg.at A ∗
          recvResultExactKeyAt A ret (M.recv st.bytes msg.bytes) ∗
          A.pool ∗ stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 48 ∗
          ((s0.sp - 4944#64) ↦₆₄ g.links.cap) ∗ ((s0.sp - 4936#64) ↦₆₄ g.links.ptr) ∗
          ((s0.sp - 4928#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
          ((s0.sp - 4920#64) ↦₆₄ g.nextRoot.cap) ∗ ((s0.sp - 4912#64) ↦₆₄ g.nextRoot.ptr) ∗
          memRegion (s0.sp - 4904#64) 40 ∗
          vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
          Drop.optProtoPqRatchetInnerAt A (s0.sp - 4864#64) pre_pb.inner ∗
          memRegion (s0.sp - 4640#64) 4544 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0 ∧ sm.readReg64 .x26 = w26)
        ?_ ?_
      · by_cases hc : g.links.cap = 0
        · have hnil : ch.links = [] := by
            rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
          have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
          have h0 : arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr [] = emp := rfl
          simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
            emp_sepConj, sepConj_emp]
          wp_steps
          rw [← sepConj_emp ((s0.sp - 4944#64) ↦₆₄ 0#64), ← h0]
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide))) (by sep_focus) ?_
          wp_call (subroutine_ok_withMemEq_of_lscl hslice_raw hcl) ⟨g.links.ptr, []⟩
          have hsp_eq : stackAt s.sp dropStack32 = stackAt (s0.sp - 4992#64) dropStack32 := by rw [hsp]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)).symm) (by sep_focus) ?_
          wp_steps
          refine align_pre (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; ac_rfl) ?_
          wp_done
        · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
          have hlsl := cap_lsl7_sub_lsl4 hcap_lt
          have hsplit : g.links.cap.toNat * 112 =
              ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
            rw [← Nat.add_mul]; congr 1; omega
          have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by
            rw [← hsplit]; omega
          have hrejoin :
              memRegion g.links.ptr (ch.links.length * 112) ∗
                memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
                  ((g.links.cap.toNat - ch.links.length) * 112) ⊢
              memRegion g.links.ptr (g.links.cap.toNat * 112) := by
            rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112)
                  ((g.links.cap.toNat - ch.links.length) * 112) hbound]
            exact Entails.refl _
          simp only [hc, ↓reduceIte]
          wp_steps
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide))) (by sep_focus) ?_
          wp_call (subroutine_ok_withMemEq_of_lscl hslice_raw hcl) ⟨g.links.ptr, ch.links⟩
          have hsp_eq : stackAt s.sp dropStack32 = stackAt (s0.sp - 4992#64) dropStack32 := by rw [hsp]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack32 (by decide)).symm) (by sep_focus) ?_
          refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
          wp_steps; wp_apply
          have hsp_eq2 : stackAt sf.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp_sf, hsp]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq2) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
          refine align_pre (by ac_rfl) ?_
          wp_done
      · intro s2 hpc2 hrun2 ⟨hsp2, ⟨htr2, hvregs2⟩, hx26_2⟩
        have hhdr80 : ((s0.sp - 4944#64) ↦₆₄ g.links.cap) ∗ ((s0.sp - 4936#64) ↦₆₄ g.links.ptr) ∗
            ((s0.sp - 4928#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
            ((s0.sp - 4920#64) ↦₆₄ g.nextRoot.cap) ∗ ((s0.sp - 4912#64) ↦₆₄ g.nextRoot.ptr) ∗
            memRegion (s0.sp - 4904#64) 40 ⊢ memRegion (s0.sp - 4944#64) 80 := by
          rw [← h56, ← h64, ← h72, ← h80, ← h88]
          exact chainPBHeaders_entails_memRegion_80 (s0.sp - 4944#64) g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr
        dsimp only [vecCapPtrDealloc]
        by_cases hnr : (g.nextRoot.cap == 0#64) = true <;>
          simp only [hnr, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
        · wp_steps
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
          refine align_pre (by ac_rfl) ?_; wp_done
        · refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
          wp_steps; wp_apply
          have hsp_eq2 : stackAt s2.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp2]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq2) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
          refine SepWP.focus_weaken hhdr80 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
          refine align_pre (by ac_rfl) ?_; wp_done
  · intro s3 hpc3 hrun3 hcl3 ⟨hsp3, ⟨htr3, hvregs3⟩, hx26_3⟩
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
    · cases hinner : pre_pb.inner with
      | none =>
        rw [hinner] at hw26
        dsimp only [InnerWordInv] at hw26
        subst hw26
        have hnone3 : (none3Cap' + 3#64 == 0#64) = true := rfl
        dsimp only [Drop.optProtoPqRatchetInnerAt]
        wp_steps
        refine SepWP.focus_weaken (optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s0.sp - 4864#64)) (by sep_focus) ?_
        refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
        refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
        refine align_pre (by ac_rfl) ?_; wp_done
      | some innerVal =>
        cases innerVal with
        | v1 v1 =>
          rw [hinner] at hw26
          dsimp only [InnerWordInv] at hw26
          dsimp only [Drop.optProtoPqRatchetInnerAt]
          unfold spqrRecvRoPlacedAt Prost.MessageMerge.v1StateJumpTablesPlacedAt
          wp_steps
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide))) (by sep_focus) ?_
          wp_call (subroutine_ok_withMemEq_of_lscl hinner_raw hcl3) ⟨s0.sp - 4864#64, v1.innerState⟩
          have hsp_eq3 : stackAt s3.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp3]
          refine SepWP.focus_weaken (Entails.of_eq hsp_eq3) (by sep_focus) ?_
          refine SepWP.focus_weaken (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm) (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin352 (by sep_focus) ?_
          refine SepWP.focus_weaken (ownFrame_join_352_4544 s0.sp) (by sep_focus) ?_
          refine align_pre (by ac_rfl) ?_; wp_done
    · intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
      exact step_epilogue_placed A M ext st msg ret s0 s4 _ R post hpost
        hpc4 hrun4 hsp4 hs0_align htr4 rfl

end CryptoVerification.SpqrV1.Top.Recv
