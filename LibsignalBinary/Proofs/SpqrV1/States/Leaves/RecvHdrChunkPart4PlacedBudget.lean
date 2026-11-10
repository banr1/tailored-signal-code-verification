/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
meta import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart3
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# `<NoHeaderReceived>::recv_hdr_chunk` (Block `369`) — Budget-Threaded Part 4

Budget-threaded `[LibsignalPlacement]` proofs on `lsProg_369 (Rust.withPanics ext)` for the
`VmPreserved` bytewise comparison loop (offsets `740 .. 764`) and MAC tag comparison +
`FreeOnlyEvs` deallocation (offsets `696 .. 800` / `1060`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_369 blkPl_369 lsmpl lsρ)
open CryptoVerification.RustHeap
  (LayoutOk vecU8)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (SepWPp.rw_pre)
open CryptoVerification.LibsignalSpqrV1
  (Bytes PolyDecoder compare_prefix inz isNonZero spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Auth
  (toBEBytes_8_length vecBufAt)
open CryptoVerification.SpqrV1.ChainProofs
  (bytesAt_false bytesAt_true)
open CryptoVerification.SpqrV1.GF.IsNonZero
  (isNonZeroSpec)
open CryptoVerification.SpqrV1.Poly.AddChunk
  (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage
  (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.Leaves
  (of_sepWP_lscro)
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
  (NoHeaderReceivedRecvHdrChunkGhost bne_one_ofNat_cons2 bytes_rem_entails_memRegion_hdr
   isNonZero_foldl_eq_compare_prefix recv_hdr_chunk_isPanic_of_mac_gt_32
   rejoin_memRegion_48_24_24 stackAt_extHook_eq_16_hdr sub_one_ofNat_cons2
   tst_ff_zeroExtend_64_false_of_bne tst_ff_zeroExtend_64_true_of_bne_false
   ule_32_sub_65_iff vecBufAt_expose_of_bytes_live vecU8_expose_nonempty_168
   xor_orr_loop_step)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (SepWPp.frame_call vecBufAt_of_bytes_live)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk VmPreserved rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget
  (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkDefsPlacedBudget
  (NoHeaderReceivedRecvHdrChunkEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart1PlacedBudget
  (RecvHdrChunkContractsPlaced allowPanic_isPanic_recvHdr_budget
   dealloc_placed_ok_at_recvHdr isNonZero_placed_ok_at_recvHdr
   panicBoundsCheckRecvHdrSym panic_at_bounds_check_placed_recvHdr
   recvHdrChunkPlacedPostQ recvHdrChunkPlacedPostQOfEnv
   recvHdrChunkPlacedPostQOfPrePostEnv recvHdrChunkPlacedPostQp
   spqrRustDeallocSym)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  addChunkTotal decodedMessageTotal DecodedMessageEnv
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length
  CryptoVerification.SpqrV1.Auth.MacHdrFacts.hdrLabel_length
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

private theorem vmPreserved_of_fields {s s' : State}
    (hbs : s'.brkStart = s.brkStart)
    (hb : s'.brk = s.brk)
    (htp : s'.tpidrEl0 = s.tpidrEl0)
    (hp : s'.physMemAvail = s.physMemAvail)
    (hmem : s'.mem = s.mem)
    (hfs : s'.fs = s.fs := by first | rfl | simp only [wp_norm, arm64_norm]) :
    VmPreserved s s' :=
  ⟨⟨hbs, hb, htp⟩, hp, fun _ => by rw [hmem], LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

private theorem vecU8_expose_nonempty_168_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (sp : BitVec 64) (bs : List (BitVec 8)) (hpos : 0 < bs.length) :
    vecU8 A.repAlloc (sp - 168#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 168#64) ↦₆₄ cap) ∗
          ((sp - 160#64) ↦₆₄ ptr) ∗
          ((sp - 152#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  rw [← A.repAlloc_live]
  exact vecU8_expose_nonempty_168 A.repAlloc sp bs hpos

private theorem vecBufAt_expose_of_bytes_live_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (hne0 : bs.length ≠ 0) (hle : bs.length < 2 ^ 63) :
    vecBufAt A.repAlloc (BitVec.ofNat 64 bs.length) ptr bs ⊢
      (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 := by
  rw [← A.repAlloc_live]
  exact vecBufAt_expose_of_bytes_live A.repAlloc ptr bs hne0 hle

private theorem vecBufAt_of_bytes_live_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (ptr : BitVec 64) (bs : List (BitVec 8)) (hne0 : bs.length ≠ 0) (hle : bs.length < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1 ⊢
      vecBufAt A.repAlloc (BitVec.ofNat 64 bs.length) ptr bs := by
  rw [← A.repAlloc_live]
  exact vecBufAt_of_bytes_live A.repAlloc ptr bs hne0 hle

/-! ## 1. Constant-Time Bytewise Comparison Loop (offsets `740 .. 764`) -/

set_option maxHeartbeats 1200000 in
theorem recv_hdr_chunk_compare_loop_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp) :
    ∀ (lhs rhs : List (BitVec 8)) (ptr_lhs ptr_rhs : BitVec 64) (acc : BitVec 8)
      (st : State) (F_loop : SepProp),
      lhs ≠ [] →
      lhs.length ≤ rhs.length →
      lhs.length ≤ 32 →
      st.pc = (blkPl_369).base + 740#64 →
      st.status = .Running →
      st.sp = s0.sp - 1648#64 →
      st.trace = s0.trace →
      calleeSavedVRegs st = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st.mem →
      st.readReg64 .x0 = BitVec.zeroExtend 64 acc →
      st.readReg64 .x8 = BitVec.ofNat 64 lhs.length →
      st.readReg64 .x9 = ptr_lhs →
      st.readReg64 .x10 = ptr_rhs →
      (∀ (st' : State),
        st'.pc = (blkPl_369).base + 764#64 →
        st'.status = .Running →
        st'.sp = s0.sp - 1648#64 →
        st'.trace = s0.trace →
        calleeSavedVRegs st' = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st'.mem →
        st'.readReg64 .x0 =
          BitVec.zeroExtend 64 ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) acc) →
        st'.readReg64 .x19 = st.readReg64 .x19 →
        st'.readReg64 .x20 = st.readReg64 .x20 →
        st'.readReg64 .x21 = st.readReg64 .x21 →
        st'.readReg64 .x22 = st.readReg64 .x22 →
        st'.readReg64 .x23 = st.readReg64 .x23 →
        st'.readReg64 .x24 = st.readReg64 .x24 →
        st'.readReg64 .x25 = st.readReg64 .x25 →
        st'.readReg64 .x26 = st.readReg64 .x26 →
        st'.readReg64 .x27 = st.readReg64 .x27 →
        st'.readReg64 .x28 = st.readReg64 .x28 →
        st'.readReg64 .x29 = st.readReg64 .x29 →
        st'.readReg64 .x30 = st.readReg64 .x30 →
        VmPreserved st st' →
        SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
          ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
          (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
          (recvHdrChunkPlacedPostQp F x s0 R)) →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
        ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R) := by
  intro lhs
  induction lhs with
  | nil =>
    intro _ _ _ _ _ _ hne
    exact (hne rfl).elim
  | cons a lhs' ih =>
    intro rhs ptr_lhs ptr_rhs acc st F_loop _ hle hle32 hpc hrun hsp htr hvregs hinv hx0 hx8 hx9 hx10 hcont
    cases rhs with
    | nil => simp at hle
    | cons b rhs' =>
      cases lhs' with
      | nil =>
        have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
        simp only [List.length_cons, List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat,
          wp_norm, arm64_norm] at hsp_norm hx0 hx8 hx9 hx10
        refine SepWPp.rw_pre (by
          rw [pointsToBytes_cons ptr_lhs a [], pointsToBytes_nil, sepConj_emp,
              pointsToBytes_cons ptr_rhs b rhs', sepConj_assoc]) ?_
        refine of_sepWP_lscro (mid := (blkPl_369).base + 764#64) hinv ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv1
        refine SepWPp.rw_pre (by
          rw [show ptr_lhs ↦₈ a ∗ ptr_rhs ↦₈ b ∗ (ptr_rhs + 1#64) ↦ₛ rhs' ∗ F_loop =
                (ptr_lhs ↦₈ a ∗ (ptr_lhs + 1#64) ↦ₛ []) ∗
                  (ptr_rhs ↦₈ b ∗ (ptr_rhs + 1#64) ↦ₛ rhs') ∗ F_loop by
                rw [pointsToBytes_nil]; ac_rfl,
              ← pointsToBytes_cons ptr_lhs a [],
              ← pointsToBytes_cons ptr_rhs b rhs']) ?_
        refine hcont _
          (by wp_norm_goal) (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv1
          ?_
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (vmPreserved_of_fields
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm]))
        · simp only [List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil,
            wp_norm, arm64_norm, *]
          exact xor_orr_loop_step acc a b
      | cons a2 lhs'' =>
        have hsub1 := sub_one_ofNat_cons2 a a2 lhs'' hle32
        have hbne1 := bne_one_ofNat_cons2 a a2 lhs'' hle32
        have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
        simp only [wp_norm, arm64_norm] at hsp_norm hx0 hx8 hx9 hx10
        refine SepWPp.rw_pre (by
          rw [pointsToBytes_cons ptr_lhs a (a2 :: lhs''),
              pointsToBytes_cons ptr_rhs b rhs']) ?_
        refine of_sepWP_lscro (mid := (blkPl_369).base + 740#64) hinv ?_
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv1
        refine SepWPp.rw_pre (show
            _ =
            ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs'')) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs') ∗
              ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop) by ac_rfl) ?_
        refine ih rhs' (ptr_lhs + 1#64) (ptr_rhs + 1#64) (acc ||| (a ^^^ b))
          _ ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop)
          (List.cons_ne_nil _ _)
          (by simp only [List.length_cons] at hle ⊢; omega)
          (by simp only [List.length_cons] at hle32 ⊢; omega)
          (by simp only [hbne1, ↓reduceIte, wp_norm, arm64_norm, *])
          (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv1
          (by simp only [wp_norm, arm64_norm, *]; exact xor_orr_loop_step acc a b)
          (by simp only [hsub1, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (fun st' hpc' hrun' hsp' htr' hvregs' hinv' hx0' hx19' hx20' hx21' hx22' hx23' hx24' hx25' hx26' hx27' hx28' hx29' hx30' hvm' => ?_)
        refine SepWPp.rw_pre (by
          rw [show ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs'')) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs') ∗
                ((ptr_lhs ↦₈ a) ∗ (ptr_rhs ↦₈ b) ∗ F_loop) =
              ((ptr_lhs ↦₈ a) ∗ ((ptr_lhs + 1#64) ↦ₛ (a2 :: lhs''))) ∗
                ((ptr_rhs ↦₈ b) ∗ ((ptr_rhs + 1#64) ↦ₛ rhs')) ∗ F_loop by ac_rfl,
              ← pointsToBytes_cons ptr_lhs a (a2 :: lhs''),
              ← pointsToBytes_cons ptr_rhs b rhs']) ?_
        exact hcont st' hpc' hrun' hsp' htr' hvregs' hinv'
          (by simpa only [List.zip_cons_cons, List.foldl_cons] using hx0')
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (VmPreserved.trans (vmPreserved_of_fields rfl rfl rfl rfl rfl) hvm')

theorem recv_hdr_chunk_compare_loop_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp) :
    ∀ (lhs rhs : List (BitVec 8)) (ptr_lhs ptr_rhs : BitVec 64) (acc : BitVec 8)
      (st : State) (F_loop : SepProp),
      lhs ≠ [] →
      lhs.length ≤ rhs.length →
      lhs.length ≤ 32 →
      st.pc = (blkPl_369).base + 740#64 →
      st.status = .Running →
      st.sp = s0.sp - 1648#64 →
      st.trace = s0.trace →
      calleeSavedVRegs st = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st.mem →
      st.readReg64 .x0 = BitVec.zeroExtend 64 acc →
      st.readReg64 .x8 = BitVec.ofNat 64 lhs.length →
      st.readReg64 .x9 = ptr_lhs →
      st.readReg64 .x10 = ptr_rhs →
      (∀ (st' : State),
        st'.pc = (blkPl_369).base + 764#64 →
        st'.status = .Running →
        st'.sp = s0.sp - 1648#64 →
        st'.trace = s0.trace →
        calleeSavedVRegs st' = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st'.mem →
        st'.readReg64 .x0 =
          BitVec.zeroExtend 64 ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) acc) →
        st'.readReg64 .x19 = st.readReg64 .x19 →
        st'.readReg64 .x20 = st.readReg64 .x20 →
        st'.readReg64 .x21 = st.readReg64 .x21 →
        st'.readReg64 .x22 = st.readReg64 .x22 →
        st'.readReg64 .x23 = st.readReg64 .x23 →
        st'.readReg64 .x24 = st.readReg64 .x24 →
        st'.readReg64 .x25 = st.readReg64 .x25 →
        st'.readReg64 .x26 = st.readReg64 .x26 →
        st'.readReg64 .x27 = st.readReg64 .x27 →
        st'.readReg64 .x28 = st.readReg64 .x28 →
        st'.readReg64 .x29 = st.readReg64 .x29 →
        st'.readReg64 .x30 = st.readReg64 .x30 →
        VmPreserved st st' →
        SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
          ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
          (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
          (recvHdrChunkPlacedPostQp F x s0 R)) →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
        ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_compare_loop_placed_wpp_ofPrePostEnv
    (PreEnv := Env) (PostEnv := Env) x st0 s0 R

theorem recv_hdr_chunk_compare_loop_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (st0 : M.σ) (s0 : State) (R : SepProp) :
    ∀ (lhs rhs : List (BitVec 8)) (ptr_lhs ptr_rhs : BitVec 64) (acc : BitVec 8)
      (st : State) (F_loop : SepProp),
      lhs ≠ [] →
      lhs.length ≤ rhs.length →
      lhs.length ≤ 32 →
      st.pc = (blkPl_369).base + 740#64 →
      st.status = .Running →
      st.sp = s0.sp - 1648#64 →
      st.trace = s0.trace →
      calleeSavedVRegs st = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st.mem →
      st.readReg64 .x0 = BitVec.zeroExtend 64 acc →
      st.readReg64 .x8 = BitVec.ofNat 64 lhs.length →
      st.readReg64 .x9 = ptr_lhs →
      st.readReg64 .x10 = ptr_rhs →
      (∀ (st' : State),
        st'.pc = (blkPl_369).base + 764#64 →
        st'.status = .Running →
        st'.sp = s0.sp - 1648#64 →
        st'.trace = s0.trace →
        calleeSavedVRegs st' = calleeSavedVRegs s0 →
        LibsignalCodeRoLoaded lsmpl st'.mem →
        st'.readReg64 .x0 =
          BitVec.zeroExtend 64 ((lhs.zip rhs).foldl (fun r (a, b) => r ||| (a ^^^ b)) acc) →
        st'.readReg64 .x19 = st.readReg64 .x19 →
        st'.readReg64 .x20 = st.readReg64 .x20 →
        st'.readReg64 .x21 = st.readReg64 .x21 →
        st'.readReg64 .x22 = st.readReg64 .x22 →
        st'.readReg64 .x23 = st.readReg64 .x23 →
        st'.readReg64 .x24 = st.readReg64 .x24 →
        st'.readReg64 .x25 = st.readReg64 .x25 →
        st'.readReg64 .x26 = st.readReg64 .x26 →
        st'.readReg64 .x27 = st.readReg64 .x27 →
        st'.readReg64 .x28 = st.readReg64 .x28 →
        st'.readReg64 .x29 = st.readReg64 .x29 →
        st'.readReg64 .x30 = st.readReg64 .x30 →
        VmPreserved st st' →
        SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
          ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
          (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
          (recvHdrChunkPlacedPostQp F x s0 R)) →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
        ((ptr_lhs ↦ₛ lhs) ∗ (ptr_rhs ↦ₛ rhs) ∗ F_loop)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_compare_loop_placed_wpp_ofEnv (Env := NoHeaderReceivedRecvHdrChunkEnv) x st0 s0 R

/-! ## 2. Full MAC Compare + Tag Dealloc (offsets `696 .. 800` / `1060`) -/

set_option maxHeartbeats 1600000 in
theorem recv_hdr_chunk_mac_compare_placed_wpp_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {PreEnv PostEnv : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (ptr_mac : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hmk_lt32 : x.self.uc.auth.macKey.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_369).base + 696#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx21 : st.readReg64 .x21 = ptr_mac)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont_err : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = true →
      st'.pc = (blkPl_369).base + 800#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R))
    (hcont_ok : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = false →
      st'.pc = (blkPl_369).base + 1060#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8 A.repAlloc (s0.sp - 168#64)
          (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfPrePostEnv M A lim F PreEnv PostEnv x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) := by
  let tag := x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)
  have htag_len : tag.length = 32 := by simp [tag]
  have htag_pos : 0 < tag.length := by omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_168_budget A s0.sp tag htag_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_tag ptr_tag
  refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_tag_ne, hlay_tag, hptr_tag_ne, hle_tag⟩
  have hrlay_tag : RustLayoutOk cap_tag.toNat 1 := ⟨hlay_tag, by decide⟩
  have ⟨_, _, hmax_tag⟩ := hlay_tag
  have hcap_tag_beq : (cap_tag == 0#64) = false := beq_false_of_ne hcap_tag_ne
  have hfree_tag : FreeOnlyEvs (rustDeallocEvents cap_tag.toNat 1) :=
    FreeOnlyEvs.singleton 1 cap_tag.toNat
  have h_inz := isNonZero_placed_ok_at_recvHdr ext
  simp only [withVmPreserved, isNonZeroSpec] at h_inz
  have h_dealloc := dealloc_placed_ok_at_recvHdr hC
  have h_pan_bounds := panic_at_bounds_check_placed_recvHdr hC
  have h_loop := @recv_hdr_chunk_compare_loop_placed_wpp_ofPrePostEnv
    _ M A lim F PreEnv PostEnv ext x st0 s0 R
  by_cases heq64 : hdrFull.length = 64
  · have hsub0 : hdrFull.length - 64 = 0 := by omega
    have hdrop_nil : hdrFull.drop 64 = [] := by
      rw [List.drop_eq_nil_iff]; omega
    have hmac_le32 : (hdrFull.drop 64).length ≤ 32 := by simp [hdrop_nil]
    have hx22_0 : st.readReg64 .x22 = 0#64 := by rw [hx22, hsub0]
    have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
    simp only [wp_norm, arm64_norm] at hsp_norm hx21 hx22_0 hx26 hx29
    clear hC h_pan_bounds h_loop hcont_err
    refine SepWPp.rw_pre (by rw [htag_len, stackAt_extHook_eq_16_hdr s0.sp, ← hsp]) ?_
    refine of_sepWP_lscro (mid := lsmpl.base 380) hinv ?_
    wp_steps_sync_pool (lsmpl.base 380)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv1
    wpp_call_lscro_recvHdr_budget h_inz (0#8 : BitVec 8) hinv1
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hvm_inz, hx0_sf, htr1⟩
    refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm_inz]) ?_
    have hfold_tag :
        (ptr_tag ↦ₛ tag) ∗ memRegion (ptr_tag + 32#64) (cap_tag.toNat - 32) ⊢
          memRegion ptr_tag cap_tag.toNat := by
      rw [← htag_len]
      exact bytes_rem_entails_memRegion_hdr ptr_tag cap_tag tag hle_tag hmax_tag
    refine SepWPp.fold hfold_tag (by sep_focus) ?_
    refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf ?_
    wp_steps_sync_pool (lsρ spqrRustDeallocSym)
    simp only [State.setMem_setMem]
    have hstack_sf :
        memRegion (s0.sp - 18032#64) 16368 ∗ stackAt st.sp 16 ⊢
          stackAt sf.sp extHookStack := by
      rw [hsp_sf, hsp, ← stackAt_extHook_eq_16_hdr s0.sp]
      exact Entails.refl _
    refine SepWP.fold hstack_sf (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv2
    wpp_call_lscro_recvHdr_budget h_dealloc (ptr_tag, cap_tag.toNat, 1, st_cur) hinv2
    refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr2 => ?_
    have hstack_back : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
      rw [hsp_sf, hsp]
    refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
    refine SepWPp.fold
      (rejoin_memRegion_48_24_24 s0.sp cap_tag ptr_tag 32#64)
      (by sep_focus) ?_
    have hcmp_nil : (compare_prefix (hdrFull.drop 64) tag != 0#8) = false := by
      simp [compare_prefix, isNonZero, inz, hdrop_nil]
    have htst := tst_ff_zeroExtend_64_true_of_bne_false (v := isNonZero 0#8) (by simp [isNonZero, inz])
    refine of_sepWP_lscro (mid := (blkPl_369).base + 1060#64) hF_sf_1 ?_
    wp_steps_sync_pool ((blkPl_369).base + 1060#64)
    simp only [State.setMem_setMem]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hinv3
    refine SepWPp.rw_pre (by sep_ac_rfl)
      (hcont_ok _ (rustDeallocEvents cap_tag.toNat 1) hfree_tag hmac_le32 hcmp_nil
        (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hinv3
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by rw [hsub0]; simp only [BitVec.ofNat_eq_ofNat, wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
  · have hge65 : 65 ≤ hdrFull.length := by omega
    have hsub_ne0 : hdrFull.length - 64 ≠ 0 := by omega
    have hdrop_len : (hdrFull.drop 64).length = hdrFull.length - 64 := List.length_drop
    have hdrop_ne0 : (hdrFull.drop 64).length ≠ 0 := by omega
    have hdrop_lt : (hdrFull.drop 64).length < 2 ^ 63 := by omega
    have hx22_ne : BitVec.ofNat 64 (hdrFull.length - 64) ≠ 0#64 := by
      intro h0
      have h1 := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
      change hdrFull.length - 64 = 0 at h1
      omega
    have hx22_beq : (BitVec.ofNat 64 (hdrFull.length - 64) == 0#64) = false :=
      beq_false_of_ne hx22_ne
    by_cases hgt32 : ¬ (hdrFull.drop 64).length ≤ 32
    · have hgt32' : ¬ (hdrFull.length - 64 ≤ 32) := by
        rwa [List.length_drop] at hgt32
      have hule_t : (32#64 : BitVec 64).ule (BitVec.ofNat 64 hdrFull.length - 65#64) = true :=
        (ule_32_sub_65_iff hge65 hmax_hdr).mpr hgt32'
      have hpan_model := recv_hdr_chunk_isPanic_of_mac_gt_32
        x.self x.epoch x.chunk receivingHdr hdrFull hepoch hadd hdec hge64 hmk_lt32 hgt32
      have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
      simp only [wp_norm, arm64_norm] at hsp_norm hx21 hx22 hx26 hx29
      clear hC h_inz h_dealloc h_loop hcont_err hcont_ok
      refine SepWPp.rw_pre (by rw [htag_len]) ?_
      apply SepWPp.of_sepWP (mid := lsρ panicBoundsCheckRecvHdrSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      exact allowPanic_isPanic_recvHdr_budget hpan_model (by simp only [wp_norm, arm64_norm, *]) hm
    · have hle32 : (hdrFull.drop 64).length ≤ 32 := Classical.not_not.mp hgt32
      have hle32' : hdrFull.length - 64 ≤ 32 := by rwa [List.length_drop] at hle32
      have hule_f : (32#64 : BitVec 64).ule (BitVec.ofNat 64 hdrFull.length - 65#64) = false := by
        rw [Bool.eq_false_iff]
        intro ht
        exact ((ule_32_sub_65_iff hge65 hmax_hdr).mp ht) hle32'
      have hexpose_mac :
          vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ⊢
            (ptr_mac ↦ₛ hdrFull.drop 64) ∗ A.live ptr_mac (hdrFull.length - 64) 1 := by
        rw [← hdrop_len]
        exact vecBufAt_expose_of_bytes_live_budget A ptr_mac (hdrFull.drop 64) hdrop_ne0 hdrop_lt
      have hfold_mac :
          (ptr_mac ↦ₛ hdrFull.drop 64) ∗ A.live ptr_mac (hdrFull.length - 64) 1 ⊢
            vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) := by
        rw [← hdrop_len]
        exact vecBufAt_of_bytes_live_budget A ptr_mac (hdrFull.drop 64) hdrop_ne0 hdrop_lt
      refine SepWPp.fold hexpose_mac (by sep_focus) ?_
      refine SepWPp.rw_pre (by rw [htag_len]) ?_
      have hsp_norm : st.readReg64 .sp = s0.sp - 1648#64 := hsp
      simp only [wp_norm, arm64_norm] at hsp_norm hx21 hx22 hx26 hx29
      clear hC h_pan_bounds
      refine of_sepWP_lscro (mid := (blkPl_369).base + 740#64) hinv ?_
      wp_steps_sync_pool ((blkPl_369).base + 740#64)
      simp only [State.setMem_setMem]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv1
      have hmac_ne_nil : hdrFull.drop 64 ≠ [] := by
        intro hnil
        have hlen0 := congrArg List.length hnil
        rw [List.length_drop, List.length_nil] at hlen0
        omega
      refine SepWPp.frame_call
        ((ptr_mac ↦ₛ hdrFull.drop 64) ∗ (ptr_tag ↦ₛ tag))
        (by sep_focus)
        (by rw [sepConj_assoc])
        (h_loop (hdrFull.drop 64) tag ptr_mac ptr_tag 0#8 _ _
          hmac_ne_nil (by rw [htag_len]; exact hle32) hle32
          (by wp_norm_goal)
          (by wp_norm_goal)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hinv1
          (by simp only [wp_norm, arm64_norm, *])
          (by rw [List.length_drop]; simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (fun st1 hpc1 hrun1 hsp1 htr1 hvregs1 hinv2 hx0_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1 hvm1 => ?_))
      refine ProofLib.SepWPp.transport_budgetPool hvm1 (hnext := ?_)
      have hsp1_norm : st1.readReg64 .sp = s0.sp - 1648#64 := hsp1
      simp only [wp_norm, arm64_norm] at hsp1_norm hx0_1 hx28_1 hx29_1 hx30_1
      refine SepWPp.fold hfold_mac (by sep_focus) ?_
      refine SepWPp.rw_pre (by rw [stackAt_extHook_eq_16_hdr s0.sp, ← hsp1]) ?_
      refine of_sepWP_lscro (mid := lsmpl.base 380) hinv2 ?_
      wp_steps_sync_pool (lsmpl.base 380)
      simp only [State.setMem_setMem]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv3
      wpp_call_lscro_recvHdr_budget h_inz
        (((hdrFull.drop 64).zip tag).foldl (fun r (a, b) => r ||| (a ^^^ b)) 0#8)
        hinv3
      refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) ?_
      rintro ⟨hvm_inz, hx0_sf, htr2⟩
      refine SepWPp.rw_pre (by rw [← A.pool_of_vmPreserved hvm_inz]) ?_
      have hfold_tag :
          (ptr_tag ↦ₛ tag) ∗ memRegion (ptr_tag + 32#64) (cap_tag.toNat - 32) ⊢
            memRegion ptr_tag cap_tag.toNat := by
        rw [← htag_len]
        exact bytes_rem_entails_memRegion_hdr ptr_tag cap_tag tag hle_tag hmax_tag
      refine SepWPp.fold hfold_tag (by sep_focus) ?_
      refine of_sepWP_lscro (mid := lsρ spqrRustDeallocSym) hF_sf ?_
      wp_steps_sync_pool (lsρ spqrRustDeallocSym)
      simp only [State.setMem_setMem]
      have hstack_sf :
          memRegion (s0.sp - 18032#64) 16368 ∗ stackAt st1.sp 16 ⊢
            stackAt sf.sp extHookStack := by
        rw [hsp_sf, hsp1, ← stackAt_extHook_eq_16_hdr s0.sp]
        exact Entails.refl _
      refine SepWP.fold hstack_sf (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hinv4
      wpp_call_lscro_recvHdr_budget h_dealloc (ptr_tag, cap_tag.toNat, 1, st_cur) hinv4
      refine CryptoVerification.SpqrV1.Auth.SepWPp.pure_left_focus _ (by sep_focus) fun htr3 => ?_
      have hstack_back : stackAt sf.sp extHookStack = stackAt (s0.sp - 1648#64) extHookStack := by
        rw [hsp_sf, hsp1]
      refine SepWPp.fold (Entails.of_eq hstack_back) (by sep_focus) ?_
      refine SepWPp.fold
        (rejoin_memRegion_48_24_24 s0.sp cap_tag ptr_tag 32#64)
        (by sep_focus) ?_
      rw [isNonZero_foldl_eq_compare_prefix] at *
      by_cases hcmp : (compare_prefix (hdrFull.drop 64) tag != 0#8) = true
      · have htst := tst_ff_zeroExtend_64_false_of_bne hcmp
        refine of_sepWP_lscro (mid := (blkPl_369).base + 800#64) hF_sf_1 ?_
        wp_steps_sync_pool ((blkPl_369).base + 800#64)
        simp only [State.setMem_setMem]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv5
        refine SepWPp.rw_pre (by sep_ac_rfl)
          (hcont_err _ (rustDeallocEvents cap_tag.toNat 1) hfree_tag hle32 hcmp
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv5
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
      · have hcmp_f : (compare_prefix (hdrFull.drop 64) tag != 0#8) = false :=
          Bool.eq_false_iff.mpr hcmp
        have htst := tst_ff_zeroExtend_64_true_of_bne_false hcmp_f
        refine of_sepWP_lscro (mid := (blkPl_369).base + 1060#64) hF_sf_1 ?_
        wp_steps_sync_pool ((blkPl_369).base + 1060#64)
        simp only [State.setMem_setMem]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        intro hinv5
        refine SepWPp.rw_pre (by sep_ac_rfl)
          (hcont_ok _ (rustDeallocEvents cap_tag.toNat 1) hfree_tag hle32 hcmp_f
            (by wp_norm_goal) (by wp_norm_goal)
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            hinv5
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))

theorem recv_hdr_chunk_mac_compare_placed_wpp_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {Env : NoHeaderReceivedRecvHdrChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (ptr_mac : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hmk_lt32 : x.self.uc.auth.macKey.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_369).base + 696#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx21 : st.readReg64 .x21 = ptr_mac)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont_err : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = true →
      st'.pc = (blkPl_369).base + 800#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R))
    (hcont_ok : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = false →
      st'.pc = (blkPl_369).base + 1060#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8 A.repAlloc (s0.sp - 168#64)
          (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQOfEnv M A lim F Env x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_mac_compare_placed_wpp_ofPrePostEnv
    (PreEnv := Env) (PostEnv := Env) hC x receivingHdr hdrFull ptr_mac st0 st_cur s0 st F_frame R
    hepoch hadd hdec hge64 hmax_hdr hmk_lt32 hpc hrun hsp hsp_s0 htr hvregs hinv
    hx21 hx22 hx26 hx29 hcont_err hcont_ok

theorem recv_hdr_chunk_mac_compare_placed_wpp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hC : RecvHdrChunkContractsPlaced M A lim ext)
    (x : NoHeaderReceivedRecvHdrChunkGhost F)
    (receivingHdr : PolyDecoder)
    (hdrFull : Bytes)
    (ptr_mac : BitVec 64)
    (st0 st_cur : M.σ)
    (s0 st : State) (F_frame R : SepProp)
    (hepoch : x.epoch = x.self.uc.epoch)
    (hadd : PolyDecoder.addChunk x.self.receiving_hdr x.chunk = .ok receivingHdr)
    (hdec : receivingHdr.decodedMessage = .ok (some hdrFull))
    (hge64 : 64 ≤ hdrFull.length)
    (hmax_hdr : hdrFull.length < 2 ^ 63)
    (hmk_lt32 : x.self.uc.auth.macKey.length < 2 ^ 32)
    (hpc : st.pc = (blkPl_369).base + 696#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 1648#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hinv : LibsignalCodeRoLoaded lsmpl st.mem)
    (hx21 : st.readReg64 .x21 = ptr_mac)
    (hx22 : st.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64))
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 hdrFull.length)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont_err : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = true →
      st'.pc = (blkPl_369).base + 800#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R))
    (hcont_ok : ∀ (st' : State) (evs_tag : List AllocEvent),
      FreeOnlyEvs evs_tag →
      (hdrFull.drop 64).length ≤ 32 →
      (compare_prefix (hdrFull.drop 64)
        (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) != 0#8) = false →
      st'.pc = (blkPl_369).base + 1060#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 1648#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      LibsignalCodeRoLoaded lsmpl st'.mem →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = ptr_mac →
      st'.readReg64 .x22 = BitVec.ofNat 64 (hdrFull.length - 64) →
      st'.readReg64 .x23 = ptr_mac →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st'
        (vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
          memRegion (s0.sp - 168#64) 48 ∗
          A.pool lim (M.stepEvents evs_tag st_cur) st' ∗
          stackAt (s0.sp - 1648#64) extHookStack ∗
          F_frame)
        (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
        (recvHdrChunkPlacedPostQp F x s0 R)) :
    SepWPp ((blkPC_369).rebase (blkPl_369).base (Rust.withPanics ext)) (s0.readReg64 .x30) st
      (vecU8 A.repAlloc (s0.sp - 168#64)
          (x.self.uc.auth.macHdrUnchecked F x.epoch (hdrFull.take 64)) ∗
        memRegion (s0.sp - 144#64) 24 ∗
        vecBufAt A.repAlloc (BitVec.ofNat 64 (hdrFull.length - 64)) ptr_mac (hdrFull.drop 64) ∗
        A.pool lim st_cur st ∗
        stackAt (s0.sp - 1648#64) extHookStack ∗
        F_frame)
      (recvHdrChunkPlacedPostQ M A lim F x st0 s0 R)
      (recvHdrChunkPlacedPostQp F x s0 R) :=
  recv_hdr_chunk_mac_compare_placed_wpp_ofEnv
    (Env := NoHeaderReceivedRecvHdrChunkEnv) hC x receivingHdr hdrFull ptr_mac st0 st_cur s0 st
    F_frame R hepoch hadd hdec hge64 hmax_hdr hmk_lt32 hpc hrun hsp hsp_s0 htr hvregs hinv
    hx21 hx22 hx26 hx29 hcont_err hcont_ok

end LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkPart4PlacedBudget
