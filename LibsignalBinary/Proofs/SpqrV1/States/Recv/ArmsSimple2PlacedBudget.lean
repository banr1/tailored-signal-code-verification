/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Budget-Threaded `HeaderReceived` Arm

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proof of `States.headerReceived`
(`tag = 8#64`, `+2268`) with `HeaderReceivedRecvPostEnv` and `VmPreserved`.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 lsProg_332 lsmpl lsρ sepWP_seq_lscl
  withLsCodeLoaded withMemEq
)
open CryptoVerification.LibsignalSpqrV1 (Message MlKem NUM_POLYS Pt States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (HeaderReceived)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec withLsCodeRoLoaded withStack)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  chunkedHeaderReceivedAt chunkedStatesAt chunkedStatesSize dropGluePoly16Stack
  unchunkedHeaderReceivedAt vecCapPtrDealloc vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyDecoderAt)
open CryptoVerification.SpqrV1.States.Leaves (
  ThreeVecWords authWordsList ct2SentWordsList ekSentWordsList relocatedHeap
  relocatedHeap_recompose subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded vecWordsList
  wordsBytes
)
open CryptoVerification.SpqrV1.States.Recv (
  StatesRecvGhost TraceCalleeSaved ValidStatesTag chunkedHeaderReceivedAt_1856_entails_err
  chunkedHeaderReceivedAt_extract_1856 chunkedStatesAt_headerReceived_unfold
  epilogueRecvOutPartA epilogueRecvOutPartB488 epilogueRecvStackPartA488 epilogueRecvStackPartB
  err_epochOutOfRange_entails_resultV1RecvAt existsWordsAtOff existsWordsWithBytesAtOff
  headerReceivedStackWords headerReceived_err_stack_combine headerReceived_out_recompose
  headerReceived_stack_entails_3632 memRegion_1856_split_224_288 memRegion_4144_split_1856_480
  memRegion_out_960_split_err optEpochSecretAt resultV1RecvAt
  selfA_headerReceived_entails_memRegion_928 sepWP_intro_ex sepWP_intro_ex_nest sepWP_intro_ex_pure
  spqrDeallocSym stackAt_statesRecvCallee_eq_allocHook stackAt_statesRecvCallee_eq_dropGluePoly16
  statesRecvArmOffset statesRecvCalleeStackX statesRecvPreInv statesRecvRoPlacedAt
  statesRecvSavedCells statesRecvStackX ule_false_of_gt ule_true_of_not_gt v1RecvSize words50List
  wordsAtOff
)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt messagePayloadAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1PlacedBudget (
  FreeOnlyEvs_to_statesRecvEnv simple_seq_vm_lscl
  subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (
  StatesRecvCalleeEnvs StatesRecvEnv
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (
  lsmpl_base_332_eq subroutine_ok_withMemEq_of_withLsCodeLoaded
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil sepWP_vm_evs_nil
  seq_evs_step seq_evs_step_lscl subroutine_ok_deallocFreeOnly
)

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

local elab "by_vm_steps_nest " tac:Lean.Parser.Tactic.tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      Lean.Meta.throwTacticEx `by_vm_steps_nest g m!"inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

/-! ## Binary Post-Envelope for `States.headerReceived` (`tag = 8#64`) -/

/-- binary post-envelope of `<States>::recv` on `States.headerReceived st` (`tag = 8#64`):
    deallocates at most the three `Unchunked.SendCt.HeaderReceived` vectors and the 16
    `PolyDecoder` `SortedSet<Pt>` vectors on `msg.epoch > st.uc.epoch`, and performs zero
    allocator calls (`evs = []`) on `¬ (msg.epoch > st.uc.epoch)`. -/
def HeaderReceivedRecvPostEnv {F : ShaCompress}
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (evs : List AllocEvent) : Prop :=
  if msg.epoch > st.uc.epoch then FreeOnlyEvs evs else evs = []

theorem HeaderReceivedRecvPostEnv_to_freeOnly {F : ShaCompress}
    {st : HeaderReceived spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {evs : List AllocEvent}
    (h : HeaderReceivedRecvPostEnv st msg evs) : FreeOnlyEvs evs := by
  unfold HeaderReceivedRecvPostEnv at h
  split at h
  · exact h
  · subst h; exact FreeOnlyEvs.nil

theorem HeaderReceivedRecvPostEnv_to_statesRecvEnv {F : ShaCompress}
    (outA selfA msgA : BitVec 64)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    {evs : List AllocEvent} (h : HeaderReceivedRecvPostEnv st msg evs) :
    StatesRecvEnv ⟨outA, selfA, msgA, .headerReceived st, msg⟩ evs :=
  FreeOnlyEvs_to_statesRecvEnv _ (HeaderReceivedRecvPostEnv_to_freeOnly h)

/-! ## `States.headerReceived` Entry `memcpy` (`+2268 -> +2284`, `0x55d30`) -/

/-- Relocatable entry `memcpy` (`+2268 -> +2284`) copying the 480-byte `HeaderReceived` payload
    from `selfA + 8` into `fsp + 1856` while establishing `VmPreserved s sm`. -/
theorem headerReceived_memcpy_2268_2284_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s : State) (fsp selfA : BitVec 64)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2268#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = selfA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2284#64) s
      (stackAt fsp allocHookStack ∗ memRegion (fsp + 1856#64) 480 ∗
       chunkedHeaderReceivedAt A (selfA + 8#64) st ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ stackAt fsp allocHookStack ∗ chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗
              memRegion (selfA + 8#64) 480 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx1
  have h480 : (480#64 : BitVec 64).toNat = 480 := by decide
  have hpre : stackAt s.sp allocHookStack ∗ memRegion (s.sp + 1856#64) 480 ∗
      chunkedHeaderReceivedAt A (s.readReg64 .x1 + 8#64) st ∗ Frame ⊢
      ((∃∗ bs : List (BitVec 8), ⌜bs.length = 480⌝ ∗
          (((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs)) ∗
       stackAt s.sp allocHookStack) ∗ (memRegion (s.sp + 1856#64) 480 ∗ Frame) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (CryptoVerification.SpqrV1.States.Recv.Relocatable.of_chunkedHeaderReceivedAt A st (s.readReg64 .x1 + 8#64)))))
      (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  apply sepWP_intro_ex_pure; intro bs hbs
  have hmemcpy : subroutine_ok ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy_sat
  dsimp only [lsProg_332, lsρ, spqrMemcpySym] at hmemcpy ⊢
  refine seq_vm_clean (mid := lsmpl.ρ "memcpy")
    (P_mid :=
      stackAt s.sp allocHookStack ∗
      ((((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs) ∗
       (memRegion (s.sp + 1856#64) 480 ∗ Frame)))
    (Q := fun sc =>
      sc.sp = s.sp ∧
      sc.readReg64 .lr = (blkPl_332).base + 2284#64 ∧
      sc.readReg64 .x0 = s.sp + 1856#64 ∧
      sc.readReg64 .x1 = s.readReg64 .x1 + 8#64 ∧
      (sc.readReg64 .x2).toNat = 480 ∧
      sc.readReg64 .x19 = s.readReg64 .x19 ∧
      sc.readReg64 .x24 = s.readReg64 .x24 ∧
      sc.readReg64 .x29 = s.readReg64 .x29 ∧
      TraceCalleeSaved sc s)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      simp only [TraceCalleeSaved, Reg.x29, h480, wp_norm, arm64_norm]
      wp_done)
  · intro sc hpcc hrunc hvm_sc ⟨hsp_c, hlr_c, hx0_c, hx1_c, hx2_c, hx19_c, hx24_c, hx29_c, htr_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hfsp_align
    refine SepWP.call_subroutine_frame hmemcpy
      (x := (s.sp + 1856#64, s.readReg64 .x1 + 8#64, bs))
      (F := relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs ∗ Frame)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro R hm
      dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack,
        allocHookStack] at hm ⊢
      rw [hbs, hsp_c, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_c, hx1_c, hx2_c⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withVmPreserved sessionMemcpySpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withVmPreserved sessionMemcpySpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf1 hpc1 hrun1 hsp1 hcs1
      dsimp only [withVmPreserved, sessionMemcpySpec, allocHookStack]
      rw [hsp_c, sepConj_assoc, sepConj_assoc]
      refine SepWP.pure_elim fun hvm1 => ?_
      refine SepWP.pure_elim fun ⟨_, htr1⟩ => ?_
      rcases hcs1 with ⟨hx19_cs, _, _, _, _, hx24_cs, _, _, _, _, hx29_cs, hsimd_cs⟩
      have hsp_1 : sf1.sp = s.sp := hsp1.trans hsp_c
      have hx19_1 : sf1.readReg64 .x19 = s.readReg64 .x19 := hx19_cs.trans hx19_c
      have hx24_1 : sf1.readReg64 .x24 = s.readReg64 .x24 := hx24_cs.trans hx24_c
      have hx29_1 : sf1.readReg64 .x29 = s.readReg64 .x29 := hx29_cs.trans hx29_c
      have htr_s1 : TraceCalleeSaved sf1 s := ⟨htr1.trans htr_c.1, hsimd_cs.trans htr_c.2⟩
      have hvm_s1 : VmPreserved s sf1 := hvm_sc.trans hvm1
      refine SepWP.done hpc1 hrun1 ⟨hvm_s1, ?_, hsp_1, hx19_1, hx24_1, hx29_1, htr_s1⟩
      rw [← hbs]
      refine Entails.trans (Entails.of_eq (show _ = stackAt s.sp 4096 ∗
        (((s.sp + 1856#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs) ∗
        ((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ Frame by sep_ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono
        (relocatedHeap_recompose (fun a => chunkedHeaderReceivedAt A a st) bs (s.sp + 1856#64))
        (sepConj_mono_left (pointsToBytes_entails_memRegion (s.readReg64 .x1 + 8#64) bs)))
    · intro _ _ _ ho
      unfold withVmPreserved sessionMemcpySpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

/-! ## `States.headerReceived` — `Ok` Branch (`¬ (msg.epoch > st.uc.epoch)`) -/

set_option maxHeartbeats 1600000 in
theorem headerReceived_ok_step_2284_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch msg_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64)
    (u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 : BitVec 64)
    (u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 : BitVec 64)
    (Frame : SepProp) (hle : ¬ (msg_epoch > st_epoch)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s
      (headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
       (msgA ↦₆₄ msg_epoch) ∗
       epilogueRecvStackPartA488 fsp u224 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 ∗
       ((fsp + 232#64) ↦₆₄ u232) ∗
       epilogueRecvStackPartB fsp u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢ headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
          (msgA ↦₆₄ msg_epoch) ∗
          epilogueRecvStackPartA488 fsp 8#64 w7 w13 w12 w10 w5 w4 w11 st_epoch w8 w3 w2 w6 ∗
          ((fsp + 232#64) ↦₆₄ noneCap) ∗
          epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w39 ∧ sm.readReg64 .x1 = w0 ∧ sm.readReg64 .x2 = w57 ∧ sm.readReg64 .x3 = w29 ∧
        sm.readReg64 .x4 = w49 ∧ sm.readReg64 .x5 = w48 ∧ sm.readReg64 .x6 = w40 ∧ sm.readReg64 .x7 = w38 ∧
        sm.readReg64 .x8 = w1 ∧ sm.readReg64 .x9 = w43 ∧ sm.readReg64 .x10 = w35 ∧ sm.readReg64 .x11 = w34 ∧
        sm.readReg64 .x12 = w33 ∧ sm.readReg64 .x13 = w52 ∧ sm.readReg64 .x14 = w53 ∧ sm.readReg64 .x15 = w36 ∧
        sm.readReg64 .x16 = w55 ∧ sm.readReg64 .x17 = w45 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = w59 ∧ sm.readReg64 .x21 = w42 ∧ sm.readReg64 .x22 = w51 ∧ sm.readReg64 .x23 = w15 ∧
        sm.readReg64 .x24 = w31 ∧ sm.readReg64 .x25 = w32 ∧ sm.readReg64 .x26 = w47 ∧ sm.readReg64 .x27 = w16 ∧
        sm.readReg64 .x28 = w37 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w41 ∧
        TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch st_epoch = true := ule_true_of_not_gt hle
  dsimp only [lsProg_332, headerReceivedStackWords,
    wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, noneCap, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx24
  by_vm_steps (
    wp_steps
    wp_done)

set_option maxHeartbeats 1600000 in
/-- Relocatable `Ok` branch (`¬ (msg.epoch > st.uc.epoch)`) of `States.headerReceived`
    (`+2284 -> s0.readReg64 .x30`) with `VmPreserved s sf`. -/
theorem states_recv_headerReceived_ok_2284_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .ok ⟨none, .headerReceived st⟩ := by
    simp only [States.recv, HeaderReceived.epoch,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.epoch, hle, ↓reduceIte]
  rw [hrecv, memRegion_1856_split_224_288 fsp]
  have hpre : stackAt fsp statesRecvCalleeStackX ∗
      (memRegion fsp 224 ∗ existsWordsAtOff fsp 36 224 ∗ memRegion (fsp + 512#64) 1344) ∗
      chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ⊢
      (existsWordsWithBytesAtOff fsp (relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek)) 50 1936 ∗
       ((∃∗ g : ThreeVecWords, wordsAtOff fsp (ekSentWordsList g st.uc.epoch) 1856 ∗
           relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
        existsWordsAtOff fsp 36 224)) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
       memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (chunkedHeaderReceivedAt_extract_1856 A fsp st)))) (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsWithBytesAtOff, existsWordsAtOff, wordsBytes, HAppend.hAppend, Append.append, List.append,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex_nest; intro w10; apply sepWP_intro_ex_nest; intro w11; apply sepWP_intro_ex_nest; intro w12; apply sepWP_intro_ex_nest; intro w13; apply sepWP_intro_ex_nest; intro w14; apply sepWP_intro_ex_nest; intro w15
  apply sepWP_intro_ex_nest; intro w16; apply sepWP_intro_ex_nest; intro w17; apply sepWP_intro_ex_nest; intro w18; apply sepWP_intro_ex_nest; intro w19; apply sepWP_intro_ex_nest; intro w20; apply sepWP_intro_ex_nest; intro w21
  apply sepWP_intro_ex_nest; intro w22; apply sepWP_intro_ex_nest; intro w23; apply sepWP_intro_ex_nest; intro w24; apply sepWP_intro_ex_nest; intro w25; apply sepWP_intro_ex_nest; intro w26; apply sepWP_intro_ex_nest; intro w27
  apply sepWP_intro_ex_nest; intro w28; apply sepWP_intro_ex_nest; intro w29; apply sepWP_intro_ex_nest; intro w30; apply sepWP_intro_ex_nest; intro w31; apply sepWP_intro_ex_nest; intro w32; apply sepWP_intro_ex_nest; intro w33
  apply sepWP_intro_ex_nest; intro w34; apply sepWP_intro_ex_nest; intro w35; apply sepWP_intro_ex_nest; intro w36; apply sepWP_intro_ex_nest; intro w37; apply sepWP_intro_ex_nest; intro w38; apply sepWP_intro_ex_nest; intro w39
  apply sepWP_intro_ex_nest; intro w40; apply sepWP_intro_ex_nest; intro w41; apply sepWP_intro_ex_nest; intro w42; apply sepWP_intro_ex_nest; intro w43; apply sepWP_intro_ex_nest; intro w44; apply sepWP_intro_ex_nest; intro w45
  apply sepWP_intro_ex_nest; intro w46; apply sepWP_intro_ex_nest; intro w47; apply sepWP_intro_ex_nest; intro w48; apply sepWP_intro_ex_nest; intro w49; apply sepWP_intro_ex_nest; intro w50; apply sepWP_intro_ex_nest; intro w51
  apply sepWP_intro_ex_nest; intro w52; apply sepWP_intro_ex_nest; intro w53; apply sepWP_intro_ex_nest; intro w54; apply sepWP_intro_ex_nest; intro w55; apply sepWP_intro_ex_nest; intro w56; apply sepWP_intro_ex_nest; intro w57
  apply sepWP_intro_ex_nest; intro w58; apply sepWP_intro_ex_nest; intro w59
  rw [sepConj_assoc (relocatedHeap _ _), sepConj_left_comm (relocatedHeap _ _)]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232; apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264
  apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280; apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312
  apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328; apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360
  apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376; apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408
  apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424; apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456
  apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472; apply sepWP_intro_ex; intro u480; apply sepWP_intro_ex; intro u488; apply sepWP_intro_ex; intro u496; apply sepWP_intro_ex; intro u504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := headerReceived_ok_step_2284_18996_placed (ext := ext) s fsp msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
    st.uc.epoch msg.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
    u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504
    u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488
    (((fsp + 240#64) ↦₆₄ u240) ∗
     relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
     relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
     memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
     memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt)
    hle hfsp_align hpc hrun hsp hx24
  refine seq_vm_clean (SepWP.weaken_pre (Entails.of_eq ?_) hstep1) ?_
  · dsimp only [headerReceivedStackWords, words50List, ekSentWordsList, vecWordsList, ct2SentWordsList, authWordsList,
      wordsBytes, HAppend.hAppend, Append.append, List.append, wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB,
      Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    sep_ac_rfl
  · intro s1 hpc1 hrun1 hvm01 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
      hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, htr1⟩
    rw [hx19] at hx19_1
    have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
    have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
    have hexit := ArmsSimple1PlacedBudget.epilogue_18996_exit_none_488_placed (A := A) hmemcpy s0 s1 outA
      8#64 u240 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0
      w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56
      (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      hsp0_align hpc1 hrun1 hsp10 hx19_1 htr10
    dsimp only at hexit; rw [← hfsp_eq] at hexit
    refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
    · have hstk3632 := headerReceived_stack_entails_3632 fsp
        g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
        st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (fsp + 512#64) 1344 ∗
         headerReceivedStackWords fsp g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
         memRegion (fsp + 2336#64) 1808) ∗
        (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
         epilogueRecvStackPartA488 fsp 8#64 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0 ∗
         ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ u240) ∗
         epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗
         statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
         (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
          relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          statesRecvRoPlacedAt)) by sep_ac_rfl))
        (Entails.trans (sepConj_mono_left hstk3632) (Entails.of_eq (by sep_ac_rfl)))
    · intro sf Pf _ _ ⟨hvm1f, hPf, hsp_f, hcs_f, htr_f⟩
      rw [hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
          hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx20_1, hx21_1,
          hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx30_1] at hPf
      have hrec := headerReceived_out_recompose A outA st g w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      refine ⟨hvm01.trans hvm1f, Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
        (epilogueRecvOutPartA outA 8#64 g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0
           g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13
           w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 w52 w53 ∗
         epilogueRecvOutPartB488 outA w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
           w44 w45 w46 w47 w50 w51 w54 w55 w56 w57 w58 w59 ∗
         memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
         relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
         relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))) ∗
        (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
         statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) by sep_ac_rfl))
        (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

theorem states_recv_headerReceived_ok_2284_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A.repAlloc (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost sf ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hbase0 : SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A.repAlloc (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ stackAt s0.sp statesRecvStackX) ∧
        (VmPreserved s sf ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)) :=
    SepWP.mono
      (states_recv_headerReceived_ok_2284_placed (A := A.repAlloc) (K := K) hmemcpy s0 s fsp outA selfA msgA
        st msg hle hfsp_eq hsp0_align hfsp_align hpc hrun hsp hx19 hx24 htr)
      fun _ _ _ _ ⟨hvm, hPf, hq⟩ => ⟨hPf, hvm, hq⟩
  have hbase := SepWP.frame_post_entails (F := A.pool lim st_cost s) hbase0
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hbase)
    fun sf Pf _ _ ⟨hPf, hvm, hspf, hcs, htrf⟩ => ?_
  refine ⟨hvm, Entails.trans hPf ?_, hspf, hcs, htrf⟩
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## `States.headerReceived` — Error Branch (`msg.epoch > st.uc.epoch`) -/

theorem headerReceived_err_step_2284_2340_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s : State) (fsp outA msgA st_epoch msg_epoch c1 p1 v_out0 v_out16 : BitVec 64) (b_out8 : BitVec 8)
    (Frame : SepProp) (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2340#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
       vecCapPtrDealloc A.repAlloc c1 p1 ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool lim st_cost s ∗
       stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
            ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
            (msgA ↦₆₄ msg_epoch) ∗ A.pool lim (M.stepEvents evs st_cost) sm ∗
            stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  dsimp only [lsProg_332, lsρ, spqrDeallocSym] at hdealloc_raw ⊢
  subst hsp hx19 hx24
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, noneCap]
  by_cases hc1 : (c1 == 0#64) = true <;>
    simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_vm_evs_nil (fun sm hvm => by
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
    by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)
  · apply sepWP_evs_dealloc c1.toNat 1
    refine seq_vm_cont (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
      wp_apply
      have hacp_1 : AllocCallPreserved s sf := by assumption
      obtain ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine align_pre_st (by sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)

theorem headerReceived_err_step_2340_2360_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s : State) (fsp c2 p2 : BitVec 64) (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2340#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2360#64) s
      (((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗
       vecCapPtrDealloc A.repAlloc c2 p2 ∗ A.pool lim st_cost s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗
            A.pool lim (M.stepEvents evs st_cost) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  dsimp only [lsProg_332, lsρ, spqrDeallocSym] at hdealloc_raw ⊢
  subst hsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hc2 : (c2 == 0#64) = true <;>
    simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_vm_evs_nil (fun sm hvm => by
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
    by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)
  · apply sepWP_evs_dealloc c2.toNat 1
    refine seq_vm_cont (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
      wp_apply
      have hacp_1 : AllocCallPreserved s sf := by assumption
      obtain ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine align_pre_st (by sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)

theorem headerReceived_err_step_2360_2380_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s : State) (fsp c3 p3 : BitVec 64) (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2360#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2380#64) s
      (((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
       vecCapPtrDealloc A.repAlloc c3 p3 ∗ A.pool lim st_cost s ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
            A.pool lim (M.stepEvents evs st_cost) sm ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  dsimp only [lsProg_332, lsρ, spqrDeallocSym] at hdealloc_raw ⊢
  subst hsp
  dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
  by_cases hc3 : (c3 == 0#64) = true <;>
    simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · refine sepWP_vm_evs_nil (fun sm hvm => by
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
    by_vm_steps (
      wp_steps
      refine align_pre_vm (by
        simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
        try sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)
  · apply sepWP_evs_dealloc c3.toNat 1
    refine seq_vm_cont (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") ?_
    by_vm_steps_nest (
      wp_steps
      refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
      wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
      wp_apply
      have hacp_1 : AllocCallPreserved s sf := by assumption
      obtain ⟨_, _, _, _, _, _, _⟩ := hacp_1
      refine align_pre_st (by sep_ac_rfl) ?_
      simp only [AllocCallPreserved, TraceCalleeSaved, wp_norm, arm64_norm]
      wp_done)

theorem headerReceived_err_step_2380_19324_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)))
    (st_cost : M.σ)
    (s : State) (fsp : BitVec 64) (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 19324#64) s
      (vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗ A.pool lim st_cost s ∗
       stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sm Pm =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pm ⊢ memRegion (fsp + 1936#64) polyArrayBytes ∗
            A.pool lim (M.stepEvents evs st_cost) sm ∗
            stackAt fsp dropGluePoly16Stack ∗ Frame) ∧
          sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s) := by
  dsimp only [lsProg_332] at hdrop ⊢
  subst hsp
  refine sepWP_seq_lscl hcl (mid := lsmpl.base 264) ?_
  wp_steps
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcl1
  dsimp only [withMemEq, dropGlueSortedSetPt16Spec, BitVec.ofNat_eq_ofNat] at hdrop_raw
  wp_call hdrop_raw (⟨s.sp + 1936#64, vecs⟩, st_cost)
  have hacp_cf : AllocCallPreserved s sf := by assumption
  have hevs_w : FreeOnlyEvs w := by assumption
  wp_steps
  refine SepWP.mono
    (post := fun s9 P9 =>
      (P9 ⊢ memRegion (s.sp + 1936#64) polyArrayBytes ∗
        A.pool lim (M.stepEvents w st_cost) s9 ∗
        stackAt s.sp dropGluePoly16Stack ∗ Frame) ∧
      (s9.sp = s.sp ∧ AllocCallPreserved s s9 ∧ TraceCalleeSaved s9 s))
    ?_
    (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_w, hp, hq⟩)
  refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
  rcases hacp_cf with ⟨_, _, _, _, _, _, _⟩
  wp_done

set_option maxHeartbeats 1200000 in
/-- Relocatable budget-threaded error branch (`msg.epoch > st.uc.epoch`) of `States.headerReceived`
    (`+2284 -> s0.readReg64 .x30`). -/
theorem states_recv_headerReceived_err_2284_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)))
    (st_cost : M.σ)
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A.repAlloc (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢ resultV1RecvAt A.repAlloc (F := F) outA ((States.headerReceived st).recv K msg) ∗
            memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
            statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, HeaderReceived.epoch,
      CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, stackAt_statesRecvCallee_eq_allocHook fsp]
  refine SepWP.fold (chunkedHeaderReceivedAt_1856_entails_err A.repAlloc fsp st) (by sep_focus) ?_
  unfold messageAt; wp_pull_exists; rename_i v_out16 b_out8 v_out0 g12 c3 p3 vecs
  wp_focus_pure; intro hvecs
  let errOut := resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg.epoch)))
  let X1 := errOut ∗ memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt
  let X2 := stackAt s0.sp statesRecvStackX
  let Q_out : State → Prop := fun sf =>
    sf.sp = s0.sp ∧ AllocCallPreserved s sf ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace
  have hstep1 := headerReceived_err_step_2284_2340_placed hdealloc st_cost s fsp outA msgA
    st.uc.epoch msg.epoch g12.v1.cap g12.v1.ptr v_out0 v_out16 b_out8
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     memRegion (fsp + 1896#64) 8 ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
     memRegion (fsp + 1920#64) 8 ∗ vecCapPtrDealloc A.repAlloc g12.v2.cap g12.v2.ptr ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
     vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hgt hfsp_align hpc hrun hsp hx19 hx24
  refine SepWP.mono
    (seq_evs_step_lscl hcl (M := M) (A := A) (lim := lim) (st := st_cost)
      (mid := (blkPl_332).base + 2340#64) (X1 := X1) (X2 := X2)
      (P_mid := fun st1 sm =>
        ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg.epoch)) ∗
        ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
        (msgA ↦₆₄ msg.epoch) ∗ A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗
        (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
         memRegion (fsp + 1872#64) 8 ∗ ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
         memRegion (fsp + 1896#64) 8 ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
         memRegion (fsp + 1920#64) 8 ∗ vecCapPtrDealloc A.repAlloc g12.v2.cap g12.v2.ptr ∗ vecCapPtrDealloc A.repAlloc c3 p3 ∗
         vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
         statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
         messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt))
      (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s0)
      (Q_out := Q_out)
      (by
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep1 ?_)
        intro sm Pm _ _ ⟨evs1, hevs1, hPm, hsp1, hacp1, htr1⟩
        exact ⟨evs1, hevs1, hPm, hsp1, hacp1, htr1.trans htr⟩)
      ?_)
    (fun sf Pf _ _ ⟨evs, hevs, hPf, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by dsimp only [X1, X2, errOut, messageAt]; sep_ac_rfl)), hq⟩)
  intro st1 s1 hpc1 hrun1 hcl1 ⟨hsp1, hacp01, htr1⟩
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA msg.epoch) (by sep_focus) ?_
  have hstep2 := headerReceived_err_step_2340_2360_placed hdealloc st1 s1 fsp g12.v2.cap g12.v2.ptr
    (errOut ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
     vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗
     memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hfsp_align hpc1 hrun1 hsp1
  refine seq_evs_step_lscl hcl1 (M := M) (A := A) (lim := lim) (st := st1)
    (mid := (blkPl_332).base + 2360#64) (X1 := X1) (X2 := X2)
    (P_mid := fun st2 sm =>
      ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
      A.pool lim st2 sm ∗ stackAt fsp allocHookStack ∗
      (errOut ∗
       ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
       (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
       memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗
       ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
       vecCapPtrDealloc A.repAlloc c3 p3 ∗ vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗
       memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
       messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt))
    (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s0)
    (Q_out := Q_out)
    (by
      refine SepWP.weaken_pre (Entails.of_eq (by dsimp only [errOut]; sep_ac_rfl)) (SepWP.mono hstep2 ?_)
      intro sm Pm _ _ ⟨evs2, hevs2, hPm, hsp2, hacp12, htr2⟩
      exact ⟨evs2, hevs2, hPm, hsp2, hacp01.trans hacp12, htr2.trans htr1⟩)
    ?_
  intro st2 s2 hpc2 hrun2 hcl2 ⟨hsp2, hacp02, htr2⟩
  have hstep3 := headerReceived_err_step_2360_2380_placed hdealloc st2 s2 fsp c3 p3
    (errOut ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
     vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hfsp_align hpc2 hrun2 hsp2
  refine seq_evs_step_lscl hcl2 (M := M) (A := A) (lim := lim) (st := st2)
    (mid := (blkPl_332).base + 2380#64) (X1 := X1) (X2 := X2)
    (P_mid := fun st3 sm =>
      ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
      A.pool lim st3 sm ∗ stackAt fsp allocHookStack ∗
      (errOut ∗
       ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
       ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
       (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
       memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
       vecPtListOf A.repAlloc (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
       messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt))
    (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s0)
    (Q_out := Q_out)
    (by
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep3 ?_)
      intro sm Pm _ _ ⟨evs3, hevs3, hPm, hsp3, hacp23, htr3⟩
      exact ⟨evs3, hevs3, hPm, hsp3, hacp02.trans hacp23, htr3.trans htr2⟩)
    ?_
  intro st3 s3 hpc3 hrun3 hcl3 ⟨hsp3, hacp03, htr3⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp)) (by sep_focus) ?_
  have hstep4 := headerReceived_err_step_2380_19324_placed hdrop st3 s3 fsp vecs hvecs.1
    (memRegion (fsp - 19552#64) 15424 ∗ errOut ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
     memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hcl3 hfsp_align hpc3 hrun3 hsp3
  refine seq_evs_step (M := M) (A := A) (lim := lim) (st := st3)
    (mid := (blkPl_332).base + 19324#64) (X1 := X1) (X2 := X2)
    (P_mid := fun st4 sm =>
      memRegion (fsp + 1936#64) polyArrayBytes ∗ A.pool lim st4 sm ∗ stackAt fsp dropGluePoly16Stack ∗
      (memRegion (fsp - 19552#64) 15424 ∗ errOut ∗
       ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
       ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
       ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
       (msgA ↦₆₄ msg.epoch) ∗ memRegion fsp 1856 ∗
       memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
       memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
       messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt))
    (Q_mid := fun sm => sm.sp = fsp ∧ AllocCallPreserved s sm ∧ TraceCalleeSaved sm s0)
    (Q_out := Q_out)
    (by
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep4 ?_)
      intro sm Pm _ _ ⟨evs4, hevs4, hPm, hsp4, hacp34, htr4⟩
      exact ⟨evs4, hevs4, hPm, hsp4, hacp03.trans hacp34, htr4.trans htr3⟩)
    ?_
  intro st4 s4 hpc4 hrun4 ⟨hsp4, hacp04, htr4⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (headerReceived_err_stack_combine fsp g12 c3 p3 st.uc.epoch) (by sep_focus) ?_
  have hsp40 : s4.sp = s0.sp - 4240#64 := by rw [hsp4, hfsp_eq]
  have hepil := DispatchPlacedBudget.states_recv_epilogue_19324_pool_placed
    (M := M) (A := A) (lim := lim) (ext := ext) st4 s0 s4 X1
    hsp0_align (by rwa [lsmpl_base_332_eq]) hrun4 hsp40 htr4
  rw [← hfsp_eq] at hepil
  refine sepWP_evs_nil ?_
  dsimp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by dsimp only [X1, errOut, messageAt]; sep_ac_rfl)) hepil)
    fun sf Pf _ _ ⟨_, hPf, hspf, hacp4f, hcs, htrf⟩ =>
      ⟨Entails.trans hPf (Entails.of_eq (by dsimp only [X2]; sep_ac_rfl)),
       hspf, hacp04.trans hacp4f, hcs, htrf⟩

/-! ## Per-Variant `subroutine_ok` Contracts for `States.headerReceived` (`tag = 8#64`) -/

/-- Two-envelope (`PreEnv` / `HeaderReceivedRecvPostEnv`) relocatable per-variant specification
    proof for `States.headerReceived st` (`tag = 8#64`), requiring no `FitsEnv` assumption on
    `PreEnv` because neither branch allocates fresh heap blocks. -/
theorem states_recv_headerReceived_placed_ok_ext_ofPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    (PreEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerReceived st) msg
          PreEnv (fun _ => HeaderReceivedRecvPostEnv st msg))) := by
  refine subroutine_ok_statesRecvVariantPlacedSpecOfPrePostEnv_of_sepWP (.headerReceived st) msg ?_
  intro outA selfA msgA st_cost s0 hcl hpc0 hrun0 hsp0_align hx0 hx1 hx2 _ _hfits _hlr_ls
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := DispatchPlacedBudget.states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A.repAlloc selfA (.headerReceived st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s0)
    hsp0_align hpc0 hrun0
  refine simple_seq_vm_lscl hcl hpro ?_
  intro s1 hpc1 hrun1 hcl1 hvm01 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1
  rw [← A.pool_of_vmPreserved hvm01, chunkedStatesAt_headerReceived_unfold]
  have hdisp := DispatchPlacedBudget.states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 8#64
    (chunkedHeaderReceivedAt A.repAlloc (selfA + 8#64) st ∗ memRegion (selfA + 488#64) 440 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s1 ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine simple_seq_vm_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hcl2 hvm12 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  rw [lsmpl_base_332_eq] at hpc2
  rw [← A.pool_of_vmPreserved hvm12]
  rw [memRegion_4144_split_1856_480 (s0.sp - 4240#64), stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
  have hmc := headerReceived_memcpy_2268_2284_placed (A := A.repAlloc) hC.hmemcpy_sat s2 (s0.sp - 4240#64) selfA st
    ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗ statesRecvRoPlacedAt ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s2 ∗
     memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗ memRegion (s0.sp - 4240#64) 1856 ∗
     memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hsp2 hx1_2
  refine simple_seq_vm_lscl hcl2 (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hmc) ?_
  intro s3 hpc3 hrun3 hcl3 hvm23 ⟨hsp3, hx19_3, hx24_3, _, htr3⟩
  rw [hx19_2] at hx19_3; rw [hx24_2] at hx24_3
  rw [← A.pool_of_vmPreserved hvm23]
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans htr1)
  have hself2 :
      stackAt (s0.sp - 4240#64) allocHookStack ∗ chunkedHeaderReceivedAt A.repAlloc (s0.sp - 4240#64 + 1856#64) st ∗
      memRegion (selfA + 8#64) 480 ∗
      ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗
       statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool lim st_cost s3 ∗
       memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 1856 ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0) ⊢
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 1856 ∗
      chunkedHeaderReceivedAt A.repAlloc (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s3 := by
    rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 8#64) 480 ∗ memRegion (selfA + 488#64) 440) ∗
      (memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) allocHookStack ∗
       memRegion (s0.sp - 4240#64) 1856 ∗
       chunkedHeaderReceivedAt A.repAlloc (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s3) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left (selfA_headerReceived_entails_memRegion_928 selfA)) (Entails.of_eq (by sep_ac_rfl)))
  refine SepWP.weaken_pre hself2 ?_
  by_cases hgt : msg.epoch > st.uc.epoch
  · refine SepWP.mono
      (states_recv_headerReceived_err_2284_placed hC.hdealloc_sat hC.hdrop_pt16 st_cost s0 s3 (s0.sp - 4240#64)
        outA selfA msgA st msg hcl3 hgt rfl hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr30)
      fun sf Pf _ _ ⟨evs, hevs, hPf, hspf, _, hcs, htrf⟩ =>
        ⟨⟨evs, by simp only [HeaderReceivedRecvPostEnv, hgt, ↓reduceIte]; exact hevs, hPf⟩,
         hspf, hcs, htrf⟩
  · refine SepWP.mono
      (states_recv_headerReceived_ok_2284_pool_placed (A := A) (lim := lim) (K := K)
        hC.hmemcpy_sat st_cost s0 s3 (s0.sp - 4240#64)
        outA selfA msgA st msg hgt rfl hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr30)
      fun sf Pf _ _ ⟨_, hPf, hspf, hcs, htrf⟩ =>
        ⟨⟨[], by simp only [HeaderReceivedRecvPostEnv, hgt, ↓reduceIte],
          by simpa only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil] using hPf⟩,
         hspf, hcs, htrf⟩

theorem states_recv_headerReceived_placed_ok_cro_ext_ofPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    {envs : StatesRecvCalleeEnvs F}
    (PreEnv : StatesRecvGhost F → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContractsOfEnv M A lim F K envs ext)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv M A lim F K (.headerReceived st) msg
          PreEnv (fun _ => HeaderReceivedRecvPostEnv st msg))) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_headerReceived_placed_ok_ext_ofPrePostEnv M A lim F K PreEnv ext hC st msg)

/-- Default `StatesRecvEnv` relocatable per-variant specification proof for
    `States.headerReceived st` (`tag = 8#64`) under `withLsCodeLoaded lsmpl`. -/
theorem states_recv_headerReceived_placed_ok_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.headerReceived st) msg)) := by
  apply subroutine_ok_outcome_intro
  rintro ⟨⟨outA, selfA, msgA⟩, st_cost⟩ R s0 hpc hrun hpre hal
  refine (states_recv_headerReceived_placed_ok_ext_ofPrePostEnv M A lim F K StatesRecvEnv ext hC st msg).mono_outcome
    ((outA, selfA, msgA), st_cost) R s0 hpc hrun hpre hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hex, hpost⟩ | ⟨hoom, hpost⟩)
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, DefsPlacedBudget.statesRecvVariantPlacedSpec,
      DefsPlacedBudget.statesRecvVariantPlacedSpecOfEnv,
      DefsPlacedBudget.statesRecvVariantPlacedSpecOfPrePostEnv] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1, HeaderReceivedRecvPostEnv_to_statesRecvEnv outA selfA msgA st msg hpost.1.2⟩,
      hpost.2⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨c, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem states_recv_headerReceived_placed_ok_cro_ext [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : DefsPlacedBudget.StatesRecvPlacedContracts M A lim F K ext)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeRoLoaded lsmpl
        (DefsPlacedBudget.statesRecvVariantPlacedSpec M A lim F K (.headerReceived st) msg)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (states_recv_headerReceived_placed_ok_ext M A lim F K ext hC st msg)

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2PlacedBudget
