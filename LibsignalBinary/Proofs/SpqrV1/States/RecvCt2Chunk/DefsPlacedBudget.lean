/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`): Budget Relocatable Specifications

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`RecvCt2ChunkPlacedOkExt*`,
`RecvCt2ChunkPlacedOkX*`) and `.rodata` placement witnesses for Block `350`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement blkPC_418 blkPl_350 blkPl_418 lsProg_350 lsmpl)
open CryptoVerification.LibsignalTripleRatchet
  (keys_ls_subroutine_ok_of_block_cro withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SpqrV1.Drop (chunkedEkSentCt1ReceivedSize)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
  (PolyDecodedMessageCall RecvCt2ChunkGhost
   ekSentCt1ReceivedAt ekSentCt1ReceivedRecvChunkResultAt recvCt2ChunkStackExt
   stackAt_recvCt2ChunkExt_eq_X)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)

/-! ## Re-Exports from `DefsPlaced` and `DefsBudget` -/

alias sckaKeyInfoPrefixSym := CryptoVerification.SpqrV1.States.RecvCt2Chunk.sckaKeyInfoPrefixSym
alias ctLabelSym := CryptoVerification.SpqrV1.States.RecvCt2Chunk.ctLabelSym
alias zeros32Sym := CryptoVerification.SpqrV1.States.RecvCt2Chunk.zeros32Sym
alias rodata_sckaKeyInfoPrefix_placed :=
  CryptoVerification.SpqrV1.States.RecvCt2Chunk.rodata_sckaKeyInfoPrefix_placed
alias rodata_ctLabel_placed :=
  CryptoVerification.SpqrV1.States.RecvCt2Chunk.rodata_ctLabel_placed
alias rodata_zeros32_placed' :=
  CryptoVerification.SpqrV1.States.RecvCt2Chunk.rodata_zeros32_placed'
alias subroutine_ok_withLsCodeRoLoaded_rodata3_keep :=
  CryptoVerification.SpqrV1.States.RecvCt2Chunk.subroutine_ok_withLsCodeRoLoaded_rodata3_keep

alias PolyDecodedMessageEnv := DefsBudget.PolyDecodedMessageEnv
alias polyDecodedMessageEnv_nonempty := DefsBudget.polyDecodedMessageEnv_nonempty
alias recvCt2MacCt2AllocEvents := DefsBudget.recvCt2MacCt2AllocEvents
alias recvCt2PreAuthUpdateEvents := DefsBudget.recvCt2PreAuthUpdateEvents
alias recvCt2HmacEvents := DefsBudget.recvCt2HmacEvents
alias RecvCt2ReserveCt1Env := DefsBudget.RecvCt2ReserveCt1Env
alias recvCt2ReserveCt1Env_nil := DefsBudget.recvCt2ReserveCt1Env_nil
alias recvCt2ReserveCt1Env_nonempty := DefsBudget.recvCt2ReserveCt1Env_nonempty
alias recvCt2ReserveCt1Env_of_doReserve := DefsBudget.recvCt2ReserveCt1Env_of_doReserve
alias OptSecret32AllocEnv := DefsBudget.OptSecret32AllocEnv
alias optSecret32AllocEnv_nil := DefsBudget.optSecret32AllocEnv_nil
alias optSecret32AllocEnv_alloc32 := DefsBudget.optSecret32AllocEnv_alloc32
alias optSecret32AllocEnv_nonempty := DefsBudget.optSecret32AllocEnv_nonempty
alias RecvCt2PostDecapsEnv := DefsBudget.RecvCt2PostDecapsEnv
alias recvCt2PostDecapsEnv_nonempty := DefsBudget.recvCt2PostDecapsEnv_nonempty
alias RecvCt2TailEnv := DefsBudget.RecvCt2TailEnv
alias recvCt2TailEnv_nonempty := DefsBudget.recvCt2TailEnv_nonempty
alias RecvCt2ChunkEnv := DefsBudget.RecvCt2ChunkEnv
alias recvCt2ChunkEnv_nonempty := DefsBudget.recvCt2ChunkEnv_nonempty
alias recvCt2ChunkEnv_of_stillReceiving := DefsBudget.recvCt2ChunkEnv_of_stillReceiving
alias recvCt2ChunkBudgetOnPanic := DefsBudget.recvCt2ChunkBudgetOnPanic

alias polyDecodedMessagePlacedSpecOfEnv := DefsBudget.polyDecodedMessagePlacedSpecOfEnv
alias polyDecodedMessagePlacedSpec := DefsBudget.polyDecodedMessagePlacedSpec
alias PolyDecodedMessagePlacedOkXOfEnv := DefsBudget.PolyDecodedMessagePlacedOkXOfEnv
alias PolyDecodedMessagePlacedOkX := DefsBudget.PolyDecodedMessagePlacedOkX
alias polyDecodedMessagePlacedOkX_of_decodedMessage :=
  DefsBudget.polyDecodedMessagePlacedOkX_of_decodedMessage
alias recvCt2ChunkPlacedSpecOfPrePostEnv := DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv
alias recvCt2ChunkPlacedSpecOfEnv := DefsBudget.recvCt2ChunkPlacedSpecOfEnv
alias recvCt2ChunkPlacedSpec := DefsBudget.recvCt2ChunkPlacedSpec
alias RecvCt2ChunkPlacedOkXOfPrePostEnv := DefsBudget.RecvCt2ChunkPlacedOkXOfPrePostEnv
alias RecvCt2ChunkPlacedOkXOfEnv := DefsBudget.RecvCt2ChunkPlacedOkXOfEnv
alias RecvCt2ChunkPlacedOkX := DefsBudget.RecvCt2ChunkPlacedOkX

/-! ## Contract-Backed (`recvCt2ChunkStackExt`) Relocatable Specifications & Lifts -/

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded relocatable (`[LibsignalPlacement]`)
    specification of `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`) with contract-backed
    stack budget `recvCt2ChunkStackExt` (`20272`B). -/
def recvCt2ChunkPlacedSpecExtOfPrePostEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧
      s.readReg64 .x1 = x.selfA ∧
      s.readReg64 .x2 = x.epoch ∧
      s.readReg64 .x3 = x.chunkA ∧
      PolyDecoderStrictSorted x.self.receiving_ct2 ∧
      x.self.uc.auth.rootKey.length + 32 < 2 ^ 63 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA chunkedEkSentCt1ReceivedSize ∗
      ekSentCt1ReceivedAt A.repAlloc x.selfA x.self ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt s.sp recvCt2ChunkStackExt
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      ekSentCt1ReceivedRecvChunkResultAt A.repAlloc x.outA
        (x.self.recv_ct2_chunk K x.epoch x.chunk) ∗
      memRegion x.selfA chunkedEkSentCt1ReceivedSize ∗
      chunkAt x.chunkA x.chunk ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp recvCt2ChunkStackExt
  onPanic := fun (x, _) s0 sf => recvCt2ChunkBudgetOnPanic K x s0 sf

/-- Single-envelope (`Env`) contract-backed relocatable specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackExt`). -/
abbrev recvCt2ChunkPlacedSpecExtOfEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkPlacedSpecExtOfPrePostEnv K F M A lim Env Env

/-- Canonical contract-backed relocatable budget specification of
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackExt`). -/
abbrev recvCt2ChunkPlacedSpecExt [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (RecvCt2ChunkGhost F × M.σ) :=
  recvCt2ChunkPlacedSpecExtOfEnv K F M A lim RecvCt2ChunkEnv

/-- Two-envelope (`PreEnv` / `PostEnv`) contract-backed relocatable contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackExt`). -/
def RecvCt2ChunkPlacedOkExtOfPrePostEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_350 (Rust.withPanics ext))
    (blkPl_350).base
    (withLsCodeRoLoaded lsmpl
      (recvCt2ChunkPlacedSpecExtOfPrePostEnv K F M A lim PreEnv PostEnv))

/-- Envelope-parametric contract-backed relocatable contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackExt`). -/
abbrev RecvCt2ChunkPlacedOkExtOfEnv [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : RecvCt2ChunkGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim Env Env ext

/-- Canonical contract-backed relocatable budget contract for
    `<EkSentCt1Received>::recv_ct2_chunk` (Block `350`, stack `recvCt2ChunkStackExt`). -/
abbrev RecvCt2ChunkPlacedOkExt [LibsignalPlacement]
    (K : MlKem) (F : ShaCompress)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  RecvCt2ChunkPlacedOkExtOfEnv K F M A lim RecvCt2ChunkEnv ext

/-- Frame the bottom `720` stack bytes (`recvCt2ChunkStackX = 19552`B ->
    `recvCt2ChunkStackExt = 20272`B) underneath `withLsCodeRoLoaded lsmpl`. -/
theorem withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X [LibsignalPlacement]
    {P : Program} {addr : BitVec 64}
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    (h : subroutine_ok P addr
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv))) :
    subroutine_ok P addr
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecExtOfPrePostEnv K F M A lim PreEnv PostEnv)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  let R' : SepProp := memRegion (s0.sp - 20272#64) 720 ∗ R
  have hpre' : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv)).pre (x, st) s0 ∗ R' := by
    dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpecExtOfPrePostEnv,
      recvCt2ChunkPlacedSpecOfPrePostEnv, DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
      R'] at hpre ⊢
    rw [stackAt_recvCt2ChunkExt_eq_X s0.sp] at hpre
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  refine h.mono_outcome (x, st) R' s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpecExtOfPrePostEnv,
      recvCt2ChunkPlacedSpecOfPrePostEnv, DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
      R'] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_recvCt2ChunkExt_eq_X s0.sp]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeRoLoaded, recvCt2ChunkPlacedSpecExtOfPrePostEnv,
      recvCt2ChunkPlacedSpecOfPrePostEnv, DefsBudget.recvCt2ChunkPlacedSpecOfPrePostEnv,
      recvCt2ChunkBudgetOnPanic, DefsBudget.recvCt2ChunkBudgetOnPanic, R'] at hpost ⊢
    have harr :
        (⌜(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗
          anyHeap) ∗ (memRegion (s0.sp - 20272#64) 720 ∗ R) =
        ⌜(x.self.recv_ct2_chunk K x.epoch x.chunk).isPanic = true ∧ s0.trace <+: sf.trace⌝ ∗
          (anyHeap ∗ memRegion (s0.sp - 20272#64) 720) ∗ R := by sep_ac_rfl
    rw [harr] at hpost
    rw [sepConj_assoc]
    exact Satisfies.mono
      (sepConj_mono_right (sepConj_mono_left (entails_anyHeap _))) hpost
  · exact (not_satisfies_false_sepConj hex).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext) :
    RecvCt2ChunkPlacedOkExtOfPrePostEnv K F M A lim PreEnv PostEnv ext :=
  withLsCodeRoLoaded_recvCt2ChunkPlacedSpecExtOfPrePostEnv_of_X h

theorem recvCt2ChunkPlacedOkExtOfEnv_of_okX [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (h : RecvCt2ChunkPlacedOkXOfEnv K F M A lim Env ext) :
    RecvCt2ChunkPlacedOkExtOfEnv K F M A lim Env ext :=
  recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX h

theorem recvCt2ChunkPlacedOkExt_of_okX [LibsignalPlacement]
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : RecvCt2ChunkPlacedOkX K F M A lim ext) :
    RecvCt2ChunkPlacedOkExt K F M A lim ext :=
  recvCt2ChunkPlacedOkExtOfPrePostEnv_of_okX h

/-! ## Cross-Block Caller Transfer Bridges -/

theorem polyDecodedMessagePlacedOfEnv_on [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : PolyDecodedMessageCall → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : PolyDecodedMessagePlacedOkXOfEnv M A lim Env ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_418).base
      (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpecOfEnv M A lim Env)) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    ((blkPC_418).rebase (blkPl_418).base (Rust.withPanics ext))
    i 418 (Rust.withPanics ext) _ _ _ _ hok _ _ _ _ hi (by decide) (by decide)

theorem polyDecodedMessagePlaced_on [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : PolyDecodedMessagePlacedOkX M A lim ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_418).base
      (withLsCodeRoLoaded lsmpl (polyDecodedMessagePlacedSpec M A lim)) :=
  polyDecodedMessagePlacedOfEnv_on hok hi

theorem recvCt2ChunkPlacedOfPrePostEnv_on [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : RecvCt2ChunkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : RecvCt2ChunkPlacedOkXOfPrePostEnv K F M A lim PreEnv PostEnv ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_350).base
      (withLsCodeRoLoaded lsmpl
        (recvCt2ChunkPlacedSpecOfPrePostEnv K F M A lim PreEnv PostEnv)) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (lsProg_350 (Rust.withPanics ext))
    i 350 (Rust.withPanics ext) _ _ _ _ hok _ _ _ _ hi (by decide) (by decide)

theorem recvCt2ChunkPlaced_on [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : RecvCt2ChunkPlacedOkX K F M A lim ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_350).base
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpec K F M A lim)) :=
  recvCt2ChunkPlacedOfPrePostEnv_on hok hi

theorem recvCt2ChunkPlacedExt_on [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {K : MlKem} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hok : RecvCt2ChunkPlacedOkExt K F M A lim ext)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_350).base
      (withLsCodeRoLoaded lsmpl (recvCt2ChunkPlacedSpecExt K F M A lim)) :=
  @keys_ls_subroutine_ok_of_block_cro _ _ callerProg
    (lsProg_350 (Rust.withPanics ext))
    i 350 (Rust.withPanics ext) _ _ _ _ hok _ _ _ _ hi (by decide) (by decide)

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget
