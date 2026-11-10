/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4Placed
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable Prologue Bridge & `decode_state` Dispatch for `spqr::recv`

Budget-threaded `SepWPpLS` prologue lift (`+0..+312`) and post-`spqr::decode_state` error/success
dispatch (`+328..+408`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.LibsignalSpqrV1
  (MlKem MsgPreamble PqRatchetState msgPreamble recvResultExactKeyAt
   spqrDecodeState spqrDeps spqrHkdfWith spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg spqrRecvStack)
open CryptoVerification.SpqrV1.Drop (optProtoPqRatchetInnerAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (TraceVRegs V1InnerHeapPred decodeStateResultAt none2Cap
   relocOptProtoPqRatchetInnerAt spqrErrorTag)
open CryptoVerification.SpqrV1.Top.Recv
  (MsgRemValid SepWPpLS bs320_entails_bs96_inner err_payload_expose
   optProtoPqRatchetInnerAt_eq_drop ownFrame_join_4544_after_decode
   ownFrame_join_4896_err_decode protoPqRatchetStateAt_entails_head32_bs96_bs224
   recv_err_words_foldX recv_of_decodeState_error recv_of_msgPreamble_error
   relocVnTailAndChainAt ret_48_split sp_sub_4992_aligned
   spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg spqrRecvRoPlacedAt
   spqrRecvSavedRegs spqrV1Recv_noPanic_of_err spqrV1Recv_noPanic_of_recv_err_true
   spqrV1Recv_recv_of_err)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open CryptoVerification.SpqrV1.Top.Send (decodeState_spqrDeps_of_spqrDecodeState_error)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 sepWP_spqrRecvPlacedPost_of_post0
   spqrRecvBudgetPanicPost spqrRecvPlacedPost spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv
   spqrRecvPlacedPostOfEnv spqrRecvPlacedPreambleFrame step_epilogue_placed_ofEnv
   step_err_msgDecode_placed step_err_msgDecode_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (seq_vm_clean step_prologue_preamble_placed)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec framelessMemcpySpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem align_pre_wp {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (hwp : SepWP prog target_pc s P' post) :
    SepWP prog target_pc s P post :=
  heq ▸ hwp

/-! ## 1. Prologue + `msg_preamble` Entry Bridge to `SepWPpLS` (`+0 .. +312`) -/

/-- Envelope-parametric lift of `step_prologue_preamble_placed` (`+0 .. +312`) into `SepWPpLS`:
    - When `msgPreamble msg.bytes = .error err`, steps through `step_err_msgDecode_placed_ofEnv`
    (`+276..+288`) and `step_epilogue_placed_ofEnv` (`+1040..+1072`) directly to `s0.readReg64 .x30`.
    - When `msgPreamble msg.bytes = .ok pre`, steps to `spqrRecvPlacedEntry + 312#64` and invokes
    `hok_tail`. -/
theorem step_prologue_to_312_placed_ofEnv {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (hnil : Env [])
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s0 ∗
      stackAt s0.sp spqrRecvStack)
    (hok_tail : ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
      msgPreamble msg.bytes = .ok pre →
      MsgRemValid msg msgPtr pre.remaining →
      s1.pc = spqrRecvPlacedEntry + 312#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 4992#64 →
      TraceVRegs s1 s0 →
      s1.readReg64 .x0 = st.v →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
      s1.readReg64 .x24 = msgPtr →
      s1.readReg64 .x25 = pre.version.zeroExtend 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s1 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  cases hpre : msgPreamble msg.bytes with
  | error err =>
    apply SepWPpLS.of_sepWPp
    apply SepWPp.of_sepWP_ret
    refine step_prologue_preamble_placed A lim st_cost ext st msg ret (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr hpc1 hrun1 hsp1 htr1 hx19_1 hP1
      have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error false :=
        spqrV1Recv_recv_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
        spqrV1Recv_noPanic_of_err (recv_of_msgPreamble_error (spqrDeps F K) (spqrHkdfWith F) herr)
      have hP1' : P1 =
          spqrRecvRoPlacedAt ∗
          st.at A.repAlloc ∗
          msg.at A.repAlloc ∗
          memRegion ret 48 ∗
          A.pool lim (MC.stepEvents [] st_cost) s1 ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 0x1320 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0 := by
        rw [hP1, AllocCostModel.stepEvents_nil]
      exact sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp
        (step_err_msgDecode_placed_ofEnv A lim st_cost Env [] hnil
          (spqrV1Recv F K) ext st msg ret s0 s1 P1 R
          _ rfl hrecv hpc1 hrun1 hsp1 hsp_align htr1 hx19_1 hP1')
    · intro pre' _ _ _ hok'
      rw [hpre] at hok'
      cases hok'
  | ok pre =>
    apply SepWPpLS.of_sepWP (mid := spqrRecvPlacedEntry + 312#64)
    refine step_prologue_preamble_placed A lim st_cost ext st msg ret
      (spqrRecvPlacedEntry + 312#64) s0 P
      (fun sm Pm =>
        SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) sm Pm
          (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
          (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R))
      ?_ ?_ hpc hrun hsp_align hx0 hx1 hx8 hP
    · intro s1 P1 herr
      rw [hpre] at herr
      cases herr
    · intro pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1
      apply SepWP.done hpc1 hrun1
      exact hok_tail pre' msgPtr s1 P1 hok' hvalid hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hP1

theorem step_prologue_to_312_placed {MC : AllocCostModel} (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (s0 : State) (P R : SepProp)
    (hpc : s0.pc = spqrRecvPlacedEntry)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = st.v)
    (hx1 : s0.readReg64 .x1 = msg.v)
    (hx8 : s0.readReg64 .x8 = ret)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cost s0 ∗
      stackAt s0.sp spqrRecvStack)
    (hok_tail : ∀ (pre : MsgPreamble) (msgPtr : BitVec 64) (s1 : State) (P1 : SepProp),
      msgPreamble msg.bytes = .ok pre →
      MsgRemValid msg msgPtr pre.remaining →
      s1.pc = spqrRecvPlacedEntry + 312#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 4992#64 →
      TraceVRegs s1 s0 →
      s1.readReg64 .x0 = st.v →
      s1.readReg64 .x19 = ret →
      s1.readReg64 .x21 = pre.index.zeroExtend 64 →
      s1.readReg64 .x22 = pre.epoch →
      s1.readReg64 .x23 = BitVec.ofNat 64 pre.remaining.length →
      s1.readReg64 .x24 = msgPtr →
      s1.readReg64 .x25 = pre.version.zeroExtend 64 →
      s1.readReg64 .x29 = s0.sp - 96#64 →
      P1 = spqrRecvPlacedPreambleFrame A lim st_cost st msg ret s0 s1 →
      SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s1 P1
        (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
        (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R)) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s0 P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_prologue_to_312_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) (SpqrBoundedEvs.nil _ _)
    F K ext st msg ret s0 P R hpc hrun hsp_align hx0 hx1 hx8 hP hok_tail

/-! ## 2. Relocatable `spqr::decode_state` Post-Call Dispatch (`+328 .. +408`) -/

/-- Envelope-parametric `Err(StateDecode)` exit at `+328` (right after `bl spqr::decode_state`)
    through `+356..+380` (`b +1040`) and `step_epilogue_placed_ofEnv` (`+1040..+1072`). -/
theorem step_decode_err_328_placed_ofEnv {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ) (Env : List AllocEvent → Prop)
    (evs : List AllocEvent) (hevs : Env evs)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (e : CryptoVerification.LibsignalSpqrV1.Error)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .error e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A.repAlloc (s0.sp - 3056#64) (.error e) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have ⟨hd_err, he_eq⟩ := decodeState_spqrDeps_of_spqrDecodeState_error F K hdec
  subst he_eq
  have hrecv : (spqrV1Recv F K).recv st.bytes msg.bytes = .error true :=
    spqrV1Recv_recv_of_err (recv_of_decodeState_error (spqrDeps F K) (spqrHkdfWith F) hpre hd_err)
  have hnp : ¬ (spqrV1Recv F K).recvPanics st.bytes msg.bytes :=
    spqrV1Recv_noPanic_of_recv_err_true hrecv
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, decodeStateResultAt,
    spqrErrorTag, none2Cap] at hpc ⊢
  refine seq_vm_clean (mid := (blkPl_329).base + 1040#64)
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      CryptoVerification.LibsignalSpqrV1.recvResultExactKeyAt A.repAlloc ret
        ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 0x1320 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun sm => sm.sp = s0.sp - 4992#64 ∧ TraceVRegs sm s0)
    ?_ ?_
  · have hexp := err_payload_expose (s0.sp - 3056#64) 0#8 343 (by decide) (by decide)
    simp only [bv_sub_add_lit, Nat.reduceSub] at hexp ⊢
    by_vm_steps (
      refine SepWP.focus_weaken hexp (by sep_focus) ?_
      wp_pull_exists; rename_i w1 w2 w3
      wp_focus_pure; intro hw1_ent
      rw [ret_48_split ret]
      wp_pull_exists; rename_i r3 r2 r1 r0
      wp_steps 14
      have hfold := recv_err_words_foldX A.repAlloc ret w1 w2 w3 0#8 true (by decide) hw1_ent
      rw [← hrecv] at hfold
      refine SepWP.fold hfold (by sep_focus) ?_
      refine SepWP.focus_weaken
        (ownFrame_join_4896_err_decode s0.sp d0 d1 d2 d3 0xFFFFFFFFFFFFFFFE#64 w1 w2 w3 w1 w2 w3)
        (by sep_focus) ?_
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm ⟨hsp1, htr1⟩
    rw [← A.pool_transport lim (MC.stepEvents evs st_cost) s s1 hvm]
    subst hpost
    exact sepWP_spqrRecvPlacedPostOfEnv_of_post0 hnp
      (step_epilogue_placed_ofEnv A lim st_cost Env evs hevs (spqrV1Recv F K) ext st msg ret
        s0 s1 _ R _ rfl hpc1 hrun1 hsp1 hs0_align htr1 rfl)

theorem step_decode_err_328_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (st msg : VecArg) (ret : BitVec 64)
    (evs : List AllocEvent) (hevs : SpqrRecvEnv st msg evs)
    (pre : MsgPreamble) (e : CryptoVerification.LibsignalSpqrV1.Error)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : spqrDecodeState st.bytes = .error e)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A.repAlloc (s0.sp - 3056#64) (.error e) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_decode_err_328_placed_ofEnv H_inner A lim st_cost (SpqrRecvEnv st msg) evs hevs
    F K ext st msg ret pre e d0 d1 d2 d3 b0 b1 b2 hpre hdec s0 s P R post hpost
    hs0_align hpc hrun hsp htr hx19 hx27 hP

/-- Budget-threaded `Ok(pre_pb)` transition at `+328` (right after `bl spqr::decode_state`)
    through `+352` (`b.ne +384`) and `+384..+404` (`bl memcpy` of `320`B) to `+408`. -/
theorem step_decode_ok_328_to_408_placed {MC : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget MC)
    (lim : BudgetLimits) (st_cur : MC.σ)
    (ext : String → Option (State → State))
    (hmemcpy_ok : subroutine_ok (spqrRecvPlacedProg ext) (lsρ "memcpy") framelessMemcpySpec)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A.repAlloc a opt =
        CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState)
    (d0 d1 d2 d3 b0 b1 b2 : BitVec 64)
    (s0 s : State) (P : SepProp) (post : State → SepProp → Prop)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 328#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx26 : s.readReg64 .x26 = s0.sp - 3056#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 3056#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) 320 ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      decodeStateResultAt H_inner A.repAlloc (s0.sp - 3056#64) (.ok pre_pb) ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ b0) ∗ ((s0.sp - 2088#64) ↦₆₄ b1) ∗ ((s0.sp - 2080#64) ↦₆₄ b2) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (htail : ∀ (w0 w1 w2 w3 : BitVec 64) (bs96 : List (BitVec 8)) (sm : State) (Pm : SepProp),
      w0 ≠ none2Cap →
      bs96.length = 96 →
      sm.pc = spqrRecvPlacedEntry + 408#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 4992#64 →
      TraceVRegs sm s0 →
      sm.readReg64 .x19 = ret →
      sm.readReg64 .x20 = w0 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x27 = s0.sp - 3056#64 →
      sm.readReg64 .x28 = s0.sp - 4288#64 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      Pm = (spqrRecvRoPlacedAt ∗
        st.at A.repAlloc ∗
        msg.at A.repAlloc ∗
        memRegion ret 48 ∗
        A.pool lim st_cur sm ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
        ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
        ((s0.sp - 4960#64) ↦ₛ bs96) ∗
        (relocVnTailAndChainAt A.repAlloc w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
        optProtoPqRatchetInnerAt A.repAlloc (s0.sp - 4864#64) pre_pb.inner ∗
        ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
        (∃∗ P_tail : SepProp,
          ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
            memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_tail) ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0) →
      SepWP (spqrRecvPlacedProg ext) (spqrRecvPlacedEntry + 408#64) sm Pm post) :
    SepWP (spqrRecvPlacedProg ext) (spqrRecvPlacedEntry + 408#64) s P post := by
  have hmemcpy_raw := hmemcpy_ok
  simp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec] at hmemcpy_raw
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true :=
    sp_sub_4992_aligned s0 hs0_align
  rcases htr with ⟨htr_eq, hvregs⟩
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry, decodeStateResultAt,
    BitVec.ofNat_eq_ofNat] at hmemcpy_raw hpc htail ⊢
  have hsplit := protoPqRatchetStateAt_entails_head32_bs96_bs224 H_inner A.repAlloc (s0.sp - 3056#64) pre_pb
  rw [bv_sub_add_lit s0.sp 3056 8, bv_sub_add_lit s0.sp 3056 16,
      bv_sub_add_lit s0.sp 3056 24, bv_sub_add_lit s0.sp 3056 32] at hsplit
  refine SepWP.focus_weaken hsplit (by sep_focus) ?_
  wp_pull_exists; rename_i w0 w1 w2 w3 bs96 bs224
  wp_focus_pure; rintro ⟨hw0_ne, hbs96, hbs224, hbs320⟩
  have hw0_cmn : (w0 + 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]
    intro heq
    apply hw0_ne
    change w0 = -2#64
    revert w0 heq; bv_kernel
  have hlen_lt : (bs96 ++ bs224).length < 2 ^ 64 := by rw [hbs320]; decide
  have hlen_eq : (320#64 : BitVec 64).toNat = (bs96 ++ bs224).length := hbs320.symm
  have hdst_eq : memRegion (s0.sp - 4960#64) (bs96 ++ bs224).length =
      memRegion (s0.sp - 4960#64) 320 := by rw [hbs320]
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      spqrRecvRoPlacedAt ∗
      st.at A.repAlloc ∗
      msg.at A.repAlloc ∗
      memRegion ret 48 ∗
      A.pool lim st_cur s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      ((s0.sp - 4992#64) ↦₆₄ d0) ∗ ((s0.sp - 4984#64) ↦₆₄ d1) ∗
      ((s0.sp - 4976#64) ↦₆₄ d2) ∗ ((s0.sp - 4968#64) ↦₆₄ d3) ∗
      memRegion (s0.sp - 4960#64) (bs96 ++ bs224).length ∗
      memRegion (s0.sp - 4640#64) 1584 ∗
      ((s0.sp - 3056#64) ↦₆₄ w0) ∗ ((s0.sp - 3048#64) ↦₆₄ w1) ∗
      ((s0.sp - 3040#64) ↦₆₄ w2) ∗ ((s0.sp - 3032#64) ↦₆₄ w3) ∗
      ((s0.sp - 3024#64) ↦ₛ (bs96 ++ bs224)) ∗
      (relocVnTailAndChainAt A.repAlloc w0 w1 pre_pb).1 (unpack64 w2 ++ unpack64 w3 ++ bs96) ∗
      (relocOptProtoPqRatchetInnerAt H_inner A.repAlloc pre_pb.inner).1 bs224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗
      memRegion (s0.sp - 2072#64) 1976 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (Q := fun s1 =>
      s1.sp = s0.sp - 4992#64 ∧
      TraceVRegs s1 s0 ∧
      s1.readReg64 .x0 = s0.sp - 4960#64 ∧
      s1.readReg64 .x1 = s0.sp - 3024#64 ∧
      s1.readReg64 .x2 = 320#64 ∧
      s1.readReg64 .x30 = (blkPl_329).base + 408#64 ∧
      s1.readReg64 .x19 = ret ∧
      s1.readReg64 .x20 = w0 ∧
      s1.readReg64 .x21 = s.readReg64 .x21 ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x23 = s.readReg64 .x23 ∧
      s1.readReg64 .x24 = s.readReg64 .x24 ∧
      s1.readReg64 .x25 = s.readReg64 .x25 ∧
      s1.readReg64 .x27 = s0.sp - 3056#64 ∧
      s1.readReg64 .x28 = s0.sp - 4288#64 ∧
      s1.readReg64 .x29 = s.readReg64 .x29)
    ?_ ?_
  · rw [← hdst_eq]
    by_vm_steps (
      wp_steps 13
      refine align_pre_wp (by sep_ac_rfl) ?_
      wp_done
    )
  · intro s1 hpc1 hrun1 hvm1 ⟨hsp1, ⟨htr1, hvregs1⟩, hx0_1, hx1_1, hx2_1, hlr1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx27_1, hx28_1, hx29_1⟩
    rw [← A.pool_transport lim st_cur s s1 hvm1]
    have hs1_align : s1.spAligned = true := by
      rw [State.spAligned, hsp1]; exact hfsp_align
    wp_call hmemcpy_raw ⟨s0.sp - 4960#64, s0.sp - 3024#64, bs96 ++ bs224⟩
    have hvm2 := ‹VmPreserved s1 _›
    let s2 : State := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
    have hvm2' : VmPreserved s1 s2 := hvm2
    rw [← A.pool_transport lim st_cur s1 s2 hvm2']
    have hbs_inner := bs320_entails_bs96_inner H_inner A.repAlloc (s0.sp - 4992#64) bs96 bs224 pre_pb hbs96 hbs224
    rw [bv_sub_add_lit s0.sp 4992 32, bv_sub_add_lit s0.sp 4992 128,
        optProtoPqRatchetInnerAt_eq_drop h_inner_eq] at hbs_inner
    refine SepWP.focus_weaken hbs_inner (by sep_focus) ?_
    let P_tail : SepProp :=
      memRegion (s0.sp - 4640#64) 1584 ∗
        ((s0.sp - 3056#64) ↦₆₄ w0) ∗ ((s0.sp - 3048#64) ↦₆₄ w1) ∗
        ((s0.sp - 3040#64) ↦₆₄ w2) ∗ ((s0.sp - 3032#64) ↦₆₄ w3) ∗
        ((s0.sp - 3024#64) ↦ₛ (bs96 ++ bs224)) ∗
        memRegion (s0.sp - 2704#64) 608 ∗
        memRegion (s0.sp - 2072#64) 1976
    have hP_tail_join :
        ((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_tail ⊢
          memRegion (s0.sp - 4640#64) 4544 := by
      refine Entails.trans (Entails.of_eq ?_)
        (ownFrame_join_4544_after_decode s0.sp w0 w1 w2 w3 w1 w2 w3 (bs96 ++ bs224) hbs320)
      unfold P_tail; sep_ac_rfl
    have hP_tail_intro :
        P_tail ⊢
          ∃∗ P_t : SepProp,
            ⌜((s0.sp - 2096#64) ↦₆₄ w1) ∗ ((s0.sp - 2088#64) ↦₆₄ w2) ∗ ((s0.sp - 2080#64) ↦₆₄ w3) ∗ P_t ⊢
              memRegion (s0.sp - 4640#64) 4544⌝ ∗ P_t :=
      Entails.sepExists_right P_tail (Entails.pure_right hP_tail_join (Entails.refl _))
    refine SepWP.focus_weaken hP_tail_intro (by unfold P_tail; sep_focus) ?_
    exact htail w0 w1 w2 w3 bs96 _ _ hw0_ne hbs96
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4PlacedBudget
