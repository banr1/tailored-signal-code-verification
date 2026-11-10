/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch
public import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WP.Apply

/-!
# Post-Arm Reassembly (`+3068..+3196`), 11-Arm Envelopes, & Continuation Helpers (Block `427`)

Defines per-arm and unified `AllocEnv` budget envelopes and proves `VmPreserved` post-arm
stack reassembly (`+3068 -> +3196`) for `<States>::send`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement libsignalSessionCode lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced of_sepWP_lscro spqrCoinsAfterPlaced spqrCoinsAtPlaced
   spqrCoinsAtPlaced_entails_after_zero)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB EpochSecret Message MlKem States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (NoHeaderReceived)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Drop (chunkedKeysSampledToCt1Received chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkSize)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.Leaves
  (Ct1ReceivedSendEkChunkGhost Ct1SampledSendCt1ChunkGhost Ct2SampledSendCt2ChunkGhost
   EkReceivedCt1SampledSendCt1ChunkGhost HeaderSentSendEkChunkGhost relocatedHeap)
open CryptoVerification.SpqrV1.Top.MessageSerialize (messageAt)
open CryptoVerification.SpqrV1.Top.Send
  (chunkedStatesTail920At chunkedStatesTail920At_590_entails_reloc chunkedStatesWord0
   keyWordsDetached memRegion_190_928_split memRegion_1bc0_16_eq_words2 memRegion_1d70_48_split
   memRegion_530_24_split optChainPBAt_eq_word0_rest optChainPBRestAt
   optChainPBRestAt_expose_word0_inv optChainPBWord0 optEpochSecretRegSlotAt
   reassemble_590_after_memcpy reassemble_chunkedStatesAt_190 sp_add_1d92_add_10 sp_add_1d92_add_4
   sp_add_1d92_add_6 sp_add_1d92_add_8 sp_add_550_add_8 sp_add_568_add_10 sp_add_568_add_4
   sp_add_568_add_6 sp_add_568_add_8 spqrSendCalleeStack spqrSendKeySlotAt
   spqrSendKeySlotAt_entails_words spqrSendPayloadSlotAt spqrSendPayloadSlotAt_entails_words
   statesSendPostArmScratch statesSendPreArmScratch tail14_formA_eq_formB
   validSendPayload words2_to_memRegion_580_16 words3_to_memRegion_530_24 words_entails_messageAt_1d70
   words_keyWordsDetached_entails_optEpochSecretRegSlotAt words_to_memRegion_38)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved coarseCostModel)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrLogLevelZeroPlacedAt spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (SpqrSendChunkEnv spqrSendChunkEnv_nonempty)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget
  (HeaderReceivedArmEnv headerReceivedArmEnv_nonempty)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
  (sepWP_lscro_with_vm)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3PlacedBudget
  (KeysUnsampledArmEnv keysUnsampledArmEnv_nonempty)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (of_sepWP_lscro_plain spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlacedBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv
   ct1ReceivedSendEkChunkEnv_nonempty ct1SampledSendCt1ChunkEnv_nonempty
   ct2SampledSendCt2ChunkEnv_nonempty ekReceivedCt1SampledSendCt1ChunkEnv_nonempty
   headerSentSendEkChunkEnv_nonempty)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  ] do
    Lean.Attribute.erase nm `arm64_norm

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_setMem_local (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg128_local (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg64_local (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg32_local (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
private theorem mem_writeReg64_setPC (s : State) (r : Reg) (v pc : BitVec 64) :
    ((s.writeReg64 r v).setPC pc).mem = s.mem := by
  cases s; cases r <;> rfl

local syntax "by_vm_lscro " term:max ppSpace term:max ppSpace "(" tacticSeq ")" : tactic
local elab_rules : tactic
  | `(tactic| by_vm_lscro $mid:term $hcrl:term ($tac:tacticSeq)) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      refine sepWP_lscro_with_vm (mid := $mid)
        (by first | exact $hcrl | (rw [mem_writeReg64_setPC]; exact $hcrl)) ?_))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let initLCtx ← Lean.getLCtx
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      let mut revData : Array (Lean.MVarId × Nat × Lean.Expr) := #[]
      for r in rem do
        let rLCtx ← r.withContext Lean.getLCtx
        let mut newFVars : Array Lean.FVarId := #[]
        for ldecl in rLCtx do
          if !ldecl.isImplementationDetail && !initLCtx.contains ldecl.fvarId then
            newFVars := newFVars.push ldecl.fvarId
        let (reverted, rRev) ← r.revert newFVars true
        let revTy ← rRev.getType
        revData := revData.push (rRev, reverted.size, revTy)
      let rec instWithDummies :
          List (Lean.MVarId × Nat × Lean.Expr) → Array Lean.Expr →
            Lean.MetaM (Lean.Expr × Array Lean.Expr)
        | [], dummies => do
          let savedMCtx ← Lean.getMCtx
          let prf ← try
            for j in [:revData.size] do
              revData[j]!.1.assign dummies[j]!
            Lean.instantiateMVars g1
          finally
            Lean.setMCtx savedMCtx
          return (prf, dummies)
        | (_, _, revTy) :: rest, dummies =>
          Lean.Meta.withLocalDeclD (`_vm_cont) revTy fun fv =>
            instWithDummies rest (dummies.push fv)
      let (prf1, dummies) ← instWithDummies revData.toList #[]
      let nArgs := e1.getAppNumArgs
      let hk := (e1.getArg! 2).consumeMData
      let e2Fn := e2.getAppFn
      let e2Args := e2.getAppArgs
      let prf2 := prf1.replace fun sub =>
        match dummies.findIdx? (fun d => d == sub) with
        | some j => some (Lean.mkMVar revData[j]!.1)
        | none =>
          if sub.isAppOfArity ``Arm64.Program.withSvc e2Args.size then
            some sub
          else if sub.isAppOfArity ``Arm64.Program.rebase nArgs &&
              (sub.getArg! 2).consumeMData.eqv hk then
            some (Lean.mkAppN e2Fn (e2Args.set! 0 sub))
          else
            none
      g.assign prf2
      let mut newRem : List Lean.MVarId := []
      for (rRev, nRev, _) in revData do
        let (_, rIntro) ← rRev.introNP nRev
        newRem := newRem ++ [rIntro]
      Lean.Elab.Tactic.setGoals (newRem ++ savedGoals.tail!)

/-! ## 1. `VmPreserved`-Propagating `memcpy` Slice Copy & Post-Arm Reassembly (`3068..3196`) -/

omit [LibsignalPlacement] in
/-- Framed `memcpy` call rule on `sessionMemcpyRegionBudgetSpec` for an explicit byte slice
    `src ↦ₛ bs`, propagating `VmPreserved s sf`. -/
theorem call_memcpy_bytes_vm {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VmPreserved s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace) hvm_sf
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.2.2

/-- Non-panicking `SepWP` + `VmPreserved` post-`States::send` reassembly epilogue
    (`spqrSendPlacedEntry + 3068#64 -> spqrSendPlacedEntry + 3196#64`). -/
theorem step_send_post_arm_3068_to_3196_placed_vm {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (chain : Option ChainPB) (msg : Message spqrPolyApi) (key : Option EpochSecret)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (hvalid : validSendPayload msg.payload)
    (hjoin : SpqrSendJoinStatePlaced sp ext s0 s msg st1)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : P = (optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      spqrSendPayloadSlotAt sp ((s.readReg64 .x24).setWidth 8) msg.payload ∗
      spqrSendKeySlotAt A.repAlloc sp (s.readReg64 .x21) (s.readReg64 .x27) key ∗
      chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      VmPreserved s sf →
      sf.pc = spqrSendPlacedEntry + 3196#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = msg.epoch →
      sf.readReg64 .x25 = sp + 0x550#64 → sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s0.readReg64 .x28 →
      (sf.readReg64 .x23 = noneCap ↔ chain = none) →
      sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) msg) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  rcases hjoin with ⟨hpc, hrun, hsp, htr, hx19, hx20, hx22, hx25, hx26, hx28, hvregs⟩
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  rw [CryptoVerification.SpqrV1.Top.ChainFrom.optChainPBAt_protoRepr_eq_exists A.repAlloc (sp + 0x60#64) chain]
  simp only [sepExists_sepConj_left]; apply SepWP.exists_elim; intro gChain
  rw [optChainPBAt_eq_word0_rest A.repAlloc gChain (sp + 0x60#64) chain]
  refine SepWP.focus_weaken (optChainPBRestAt_expose_word0_inv A.repAlloc gChain (sp + 0x60#64) chain) (by sep_focus) ?_
  wp_focus_pure; intro hchain_iff
  refine SepWP.focus_weaken (chunkedStatesTail920At_590_entails_reloc A.repAlloc sp st1) (by sep_focus) ?_
  wp_pull_exists; rename_i bs920 sw1 sw2 sw3 bs896
  wp_focus_pure; rintro ⟨hbs920, hlen896⟩
  refine SepWP.focus_weaken (spqrSendPayloadSlotAt_entails_words sp ((s.readReg64 .x24).setWidth 8) msg.payload) (by sep_focus) ?_
  wp_pull_exists; rename_i pw0 pw1 pw2 pw3 pw4 pad32
  wp_focus_pure; rintro ⟨hw24, hpay_rec⟩
  refine SepWP.focus_weaken (spqrSendKeySlotAt_entails_words A.repAlloc sp (s.readReg64 .x21) (s.readReg64 .x27) key) (by sep_focus) ?_
  wp_pull_exists; rename_i kw0 kw1
  rw [memRegion_190_928_split sp, memRegion_530_24_split sp,
      memRegion_1bc0_16_eq_words2 sp, memRegion_1d70_48_split sp]
  wp_pull_exists
  by_vm_lscro (lsρ "memcpy") hinv (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m1 hvm_m1 => ?_⟩)
  refine of_sepWP_lscro_plain (mid := (blkPl_427).base + 3108#64) hcrl_m1 ?_
  refine call_memcpy_bytes_vm hmemcpy (sp + 0x1b0#64) (sp + 0x5a8#64) hlen896
    (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A.repAlloc gChain (sp + 0x60#64) chain ∗
      ((sp + 0x190#64) ↦₆₄ _) ∗ ((sp + 0x198#64) ↦₆₄ _) ∗ ((sp + 0x1a0#64) ↦₆₄ _) ∗ ((sp + 0x1a8#64) ↦₆₄ _) ∗
      ((sp + 0x530#64) ↦₆₄ sw1) ∗ ((sp + 0x538#64) ↦₆₄ sw2) ∗ ((sp + 0x540#64) ↦₆₄ sw3) ∗
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗ ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ∗ ((sp + 0x580#64) ↦₆₄ kw0) ∗ ((sp + 0x588#64) ↦₆₄ kw1) ∗
      keyWordsDetached A.repAlloc (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1 ∗
      ((sp + 0x590#64) ↦₆₄ sw1) ∗ ((sp + 0x598#64) ↦₆₄ sw2) ∗ ((sp + 0x5a0#64) ↦₆₄ sw3) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A.repAlloc dst st1) bs920 ∗
      ((sp + 0x1bc0#64) ↦₆₄ _) ∗ ((sp + 0x1bc8#64) ↦₆₄ _) ∗ ((sp + 0x1d70#64) ↦₆₄ _) ∗ ((sp + 0x1d78#64) ↦₈ _) ∗
      ((sp + 0x1d79#64) ↦₈ _) ∗ ((sp + 0x1d7a#64) ↦₆₄ _) ∗ ((sp + 0x1d82#64) ↦₆₄ _) ∗ ((sp + 0x1d8a#64) ↦₆₄ _) ∗
      ((sp + 0x1d92#64) ↦₆₄ _) ∗ ((sp + 0x1d9a#64) ↦₁₆ _) ∗ ((sp + 0x1d9c#64) ↦₃₂ _) ∗ Frame)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 3108#64) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm]) (by sep_ac_rfl) ?_
  intro sm hpc_m hrun_m hsp_m htr_m hvm_m2 hx19_m hx20_m hx21_m hx22_m _ hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  apply SepWP.done hpc_m hrun_m; intro hcrl_m
  simp only [wp_norm, arm64_norm, *] at hx19_m hx20_m hx21_m hx22_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  have h568_to_B :
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  have h1d92_to_B (dw4 : BitVec 16) (dpad32 : BitVec 32) :
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ dw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ dpad32) ⊢
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (dpad32 ++ dw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x1d92#64) pw3 dw4 dpad32
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  by_vm_lscro ((blkPl_427).base + 3196#64) hcrl_m (
    wp_steps
    refine SepWP.focus_weaken h568_to_B (by sep_focus) ?_
    wp_steps
    refine SepWP.focus_weaken (h1d92_to_B _ _) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_f hvm_m3 => ?_⟩)
  have h568_to_A :
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32).symm
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  have h1d92_to_A :
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ pw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x1d92#64) pw3 pw4 pad32).symm
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken h568_to_A (by sep_focus) ?_
  refine SepWP.focus_weaken h1d92_to_A (by sep_focus) ?_
  have h550_38 :
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗
      ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      memRegion (sp + 0x550#64) 38 := by
    have h := words_to_memRegion_38 (sp + 0x550#64) pw0 pw1 pw2 pw3 pw4 pad32
    rwa [sp_add_550_add_8 sp,
         show (sp + 0x550#64) + 16#64 = sp + 0x560#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 24#64 = sp + 0x568#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 32#64 = sp + 0x570#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 34#64 = sp + 0x572#64 by rw [BitVec.add_assoc]; rfl] at h
  have hchain_recompose :
      ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A.repAlloc gChain (sp + 0x60#64) chain ⊢
      optChainPBAt A.repAlloc (sp + 0x60#64) chain := by
    rw [← optChainPBAt_eq_word0_rest A.repAlloc gChain (sp + 0x60#64) chain]
    exact CryptoVerification.SpqrV1.Top.ChainFrom.optChainPBAt_entails_protoRepr A.repAlloc gChain (sp + 0x60#64) chain
  refine SepWP.focus_weaken hchain_recompose (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_chunkedStatesAt_190 A.repAlloc sp st1 sw1 sw2 sw3 hbs920) (by sep_focus) ?_
  refine SepWP.focus_weaken (words3_to_memRegion_530_24 sp sw1 sw2 sw3) (by sep_focus) ?_
  refine SepWP.focus_weaken h550_38 (by sep_focus) ?_
  refine SepWP.focus_weaken (words2_to_memRegion_580_16 sp kw0 kw1) (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_590_after_memcpy sp sw1 sw2 sw3 hlen896) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (words_keyWordsDetached_entails_optEpochSecretRegSlotAt A.repAlloc sp (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (words_entails_messageAt_1d70 sp msg pw0 pw1 pw2 pw3 pw4 pad32 hvalid hpay_rec) (by sep_focus) ?_
  refine SepWP.weaken_pre ?_ (hnext _ hcrl_f (hvm_m1.trans (hvm_m2.trans hvm_m3))
    (by simp only [spqrSendPlacedEntry, wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]))
  simp only [wp_norm, arm64_norm, *]; exact Entails.of_eq (by sep_ac_rfl)

/-- Pool-threading non-panicking `SepWP` post-`States::send` reassembly epilogue
    (`spqrSendPlacedEntry + 3068#64 -> spqrSendPlacedEntry + 3196#64`). -/
theorem step_send_post_arm_3068_to_3196_sepWP_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (chain : Option ChainPB) (msg : Message spqrPolyApi) (key : Option EpochSecret)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (hvalid : validSendPayload msg.payload)
    (hjoin : SpqrSendJoinStatePlaced sp ext s0 s msg st1)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : P = (optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      spqrSendPayloadSlotAt sp ((s.readReg64 .x24).setWidth 8) msg.payload ∗
      spqrSendKeySlotAt A.repAlloc sp (s.readReg64 .x21) (s.readReg64 .x27) key ∗
      chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      A.pool lim st_b s) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3196#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = msg.epoch →
      sf.readReg64 .x25 = sp + 0x550#64 → sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s0.readReg64 .x28 →
      (sf.readReg64 .x23 = noneCap ↔ chain = none) →
      sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
          A.pool lim st_b sf) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  refine step_send_post_arm_3068_to_3196_placed_vm A lim ext hA sp chain msg key st1
    hvalid hjoin hsp_align hinv (Frame := A.pool lim st_b s ∗ Frame)
    (by rw [hP]; sep_ac_rfl) fun sf hcrl_f hvm hpc_f hrun_f hsp_f htr_f hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 hch hz hvregs => ?_
  refine SepWP.weaken_pre ?_
    (hnext sf hcrl_f hpc_f hrun_f hsp_f htr_f hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 hch hz hvregs)
  rw [A.pool_of_vmPreserved hvm]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Panic-aware `SepWPp` post-`States::send` reassembly epilogue
    (`spqrSendPlacedEntry + 3068#64 -> spqrSendPlacedEntry + 3196#64`), polymorphic in `panicPost`. -/
theorem step_send_post_arm_3068_to_3196_placed {F : ShaCompress}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s : State} (sp : BitVec 64)
    (chain : Option ChainPB) (msg : Message spqrPolyApi) (key : Option EpochSecret)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (hvalid : validSendPayload msg.payload)
    (hjoin : SpqrSendJoinStatePlaced sp ext s0 s msg st1)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : P = (optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      spqrSendPayloadSlotAt sp ((s.readReg64 .x24).setWidth 8) msg.payload ∗
      spqrSendKeySlotAt A.repAlloc sp (s.readReg64 .x21) (s.readReg64 .x27) key ∗
      chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      A.pool lim st_b s) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3196#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = msg.epoch →
      sf.readReg64 .x25 = sp + 0x550#64 → sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s0.readReg64 .x28 →
      (sf.readReg64 .x23 = noneCap ↔ chain = none) →
      sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          optEpochSecretRegSlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
          A.pool lim st_b sf) ∗ Frame) post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3196#64) hinv
  refine step_send_post_arm_3068_to_3196_sepWP_placed A lim st_b ext hA sp chain msg key st1
    hvalid hjoin hsp_align hinv hP
    fun sf hcrl_f hpc_f hrun_f hsp_f htr_f hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 hch hz hvregs => ?_
  exact SepWP.done hpc_f hrun_f fun _ =>
    hnext sf hcrl_f hpc_f hrun_f hsp_f htr_f hx19 hx20 hx21 hx22 hx25 hx26 hx27 hx28 hch hz hvregs

/-! ## 2. Constructive 11-Arm `<States>::send` Allocation-Event Envelopes & Non-Vacuity -/

/-- Envelope-parametric allocation-event envelope for `<States>::send` + post-arm reassembly
    (`statesSendArmOffset st0 -> +3196` in Block `427`), parameterized over the five leaf-call
    envelopes (`HeaderSent`, `Ct1Received` shared with `KeysSampled`, `Ct1Sampled`,
    `EkReceivedCt1Sampled`, and `Ct2Sampled`). Zero `∃`, zero `ValidRustAllocEv`. -/
def StatesSendEnvOfEnv (F : ShaCompress) (K : MlKem)
    (EnvHsEk : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop)
    (EnvCt1rEk : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop)
    (EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop)
    (EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop)
    (sp : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes)
    (evs : List AllocEvent) : Prop :=
  match st0 with
  | .keysUnsampled st =>
    match st.send_hdr_chunk K spqrPolyApi tape with
    | .ok (outSt, chunk, _) => KeysUnsampledArmEnv F K st outSt.sending_hdr chunk tape evs
    | .error _ => evs = []
  | .keysSampled st =>
    match st.send_hdr_chunk with
    | .ok (outSt, chunk) =>
      EnvCt1rEk
        { outA := sp + 0x1260#64, stA := sp + 0x958#64,
          st := chunkedKeysSampledToCt1Received st,
          outSt := chunkedKeysSampledToCt1Received outSt, chunk := chunk } evs
    | .error _ => evs = []
  | .headerSent st =>
    match st.send_ek_chunk with
    | .ok (outSt, chunk) =>
      EnvHsEk { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs
    | .error _ => evs = []
  | .ct1Received st =>
    match st.send_ek_chunk with
    | .ok (outSt, chunk) =>
      EnvCt1rEk { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs
    | .error _ => evs = []
  | .ekSentCt1Received _ => evs = []
  | .noHeaderReceived _ => evs = []
  | .headerReceived st =>
    match st.send_ct1_chunk K tape with
    | .ok (outSt, chunk, _, _) => HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk evs
    | .error _ => evs = []
  | .ct1Sampled st =>
    match st.send_ct1_chunk with
    | .ok (outSt, chunk) =>
      EnvCt1sCt1 { outA := sp + 0x1260#64, stA := sp + 0x950#64, st := st, outSt := outSt, chunk := chunk } evs
    | .error _ => evs = []
  | .ekReceivedCt1Sampled st =>
    match st.send_ct1_chunk with
    | .ok (outSt, chunk) =>
      EnvEkrCt1 { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs
    | .error _ => evs = []
  | .ct1Acknowledged _ => evs = []
  | .ct2Sampled st =>
    match st.send_ct2_chunk with
    | .ok (outSt, chunk) =>
      EnvCt2sCt2 { outA := sp + 0x1260#64, stA := sp + 0x958#64, st := st, outSt := outSt, chunk := chunk } evs
    | .error _ => evs = []

/-- Peer-seam default (`SpqrSendChunkEnv` on leaves) allocation-event envelope for
    `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`), independent of `sp`. -/
def StatesSendEnv (F : ShaCompress) (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) : List AllocEvent → Prop :=
  StatesSendEnvOfEnv F K
    (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv)
    (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) 0#64 st0 tape

theorem statesSendEnvOfEnv_default_eq (F : ShaCompress) (K : MlKem)
    (sp : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    StatesSendEnvOfEnv F K
      (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv)
      (fun _ => SpqrSendChunkEnv) (fun _ => SpqrSendChunkEnv) sp st0 tape =
    StatesSendEnv F K st0 tape := by
  funext evs; cases st0 <;> rfl

/-- Exact leaf-envelope (`*Send*ChunkEnv` on leaves) allocation-event envelope for
    `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`), independent of `sp`. -/
def StatesSendTightEnv (F : ShaCompress) (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) : List AllocEvent → Prop :=
  StatesSendEnvOfEnv F K
    HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv
    EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv 0#64 st0 tape

theorem statesSendEnvOfEnv_tight_eq (F : ShaCompress) (K : MlKem)
    (sp : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    StatesSendEnvOfEnv F K
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv
      EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv sp st0 tape =
    StatesSendTightEnv F K st0 tape := by
  funext evs
  cases st0 <;>
    simp only [StatesSendTightEnv, StatesSendEnvOfEnv, HeaderSentSendEkChunkEnv,
      Ct1ReceivedSendEkChunkEnv, Ct1SampledSendCt1ChunkEnv,
      EkReceivedCt1SampledSendCt1ChunkEnv, Ct2SampledSendCt2ChunkEnv]

theorem statesSendEnvOfEnv_nonempty (F : ShaCompress) (K : MlKem)
    {EnvHsEk : HeaderSentSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1rEk : Ct1ReceivedSendEkChunkGhost F → List AllocEvent → Prop}
    {EnvCt1sCt1 : Ct1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvEkrCt1 : EkReceivedCt1SampledSendCt1ChunkGhost F → List AllocEvent → Prop}
    {EnvCt2sCt2 : Ct2SampledSendCt2ChunkGhost F → List AllocEvent → Prop}
    (hHs : ∀ x, ∃ evs, EnvHsEk x evs)
    (hCt1r : ∀ x, ∃ evs, EnvCt1rEk x evs)
    (hCt1s : ∀ x, ∃ evs, EnvCt1sCt1 x evs)
    (hEkr : ∀ x, ∃ evs, EnvEkrCt1 x evs)
    (hCt2s : ∀ x, ∃ evs, EnvCt2sCt2 x evs)
    (sp : BitVec 64) (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    ∃ evs, StatesSendEnvOfEnv F K EnvHsEk EnvCt1rEk EnvCt1sCt1 EnvEkrCt1 EnvCt2sCt2 sp st0 tape evs := by
  cases st0 with
  | keysUnsampled st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact keysUnsampledArmEnv_nonempty F K st _ _ tape
    · exact ⟨[], rfl⟩
  | keysSampled st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hCt1r _
    · exact ⟨[], rfl⟩
  | headerSent st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hHs _
    · exact ⟨[], rfl⟩
  | ct1Received st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hCt1r _
    · exact ⟨[], rfl⟩
  | ekSentCt1Received _ => exact ⟨[], rfl⟩
  | noHeaderReceived _ => exact ⟨[], rfl⟩
  | headerReceived st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact headerReceivedArmEnv_nonempty
        { rootKey := { cap := 32#64, ptr := 1#64 }, macKey := { cap := 32#64, ptr := 1#64 } }
        st.uc.auth.rootKey.length _ _
    · exact ⟨[], rfl⟩
  | ct1Sampled st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hCt1s _
    · exact ⟨[], rfl⟩
  | ekReceivedCt1Sampled st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hEkr _
    · exact ⟨[], rfl⟩
  | ct1Acknowledged _ => exact ⟨[], rfl⟩
  | ct2Sampled st =>
    dsimp only [StatesSendEnvOfEnv]
    split
    · exact hCt2s _
    · exact ⟨[], rfl⟩

theorem statesSendEnv_nonempty (F : ShaCompress) (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    ∃ evs, StatesSendEnv F K st0 tape evs :=
  statesSendEnvOfEnv_nonempty F K
    (fun _ => spqrSendChunkEnv_nonempty) (fun _ => spqrSendChunkEnv_nonempty)
    (fun _ => spqrSendChunkEnv_nonempty) (fun _ => spqrSendChunkEnv_nonempty)
    (fun _ => spqrSendChunkEnv_nonempty) 0#64 st0 tape

theorem statesSendTightEnv_nonempty (F : ShaCompress) (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    ∃ evs, StatesSendTightEnv F K st0 tape evs :=
  statesSendEnvOfEnv_nonempty F K
    headerSentSendEkChunkEnv_nonempty ct1ReceivedSendEkChunkEnv_nonempty
    ct1SampledSendCt1ChunkEnv_nonempty ekReceivedCt1SampledSendCt1ChunkEnv_nonempty
    ct2SampledSendCt2ChunkEnv_nonempty 0#64 st0 tape

-- Concrete `coarseCostModel` non-vacuity check for `StatesSendEnv` and `StatesSendTightEnv`.
example (F : ShaCompress) (K : MlKem)
    (st : NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (tape : Bytes) :
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      coarseCostModel.init
      (StatesSendEnv F K (.noHeaderReceived st) tape) ∧
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      coarseCostModel.init
      (StatesSendTightEnv F K (.noHeaderReceived st) tape) := by
  dsimp only [StatesSendEnv, StatesSendTightEnv, StatesSendEnvOfEnv]
  exact ⟨FitsEnv.eq_iff.mpr trivial, FitsEnv.eq_iff.mpr trivial⟩

/-! ## 3. Scratch-Splitting Lemmas & Post-Arm Continuation Wrappers (`+3068 -> +3196`) -/

theorem spqrCoinsAtPlaced_entails_after_same (a cur : BitVec 64) (tape : List (BitVec 8)) :
    spqrCoinsAtPlaced a cur tape ⊢ spqrCoinsAfterPlaced a cur tape (tape.length - tape.length) := by
  rw [Nat.sub_self]; exact spqrCoinsAtPlaced_entails_after_zero a cur tape

omit [LibsignalPlacement] in
theorem memRegion_190_928_eq (sp : BitVec 64) :
    memRegion (sp + 0x190#64) 928 = memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1320#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 400#64) (n := 920) (k := 8)
    (b' := sp + 1320#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
theorem memRegion_4080_104_eq (sp : BitVec 64) :
    memRegion (sp + 4080#64) 104 = memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 4128#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4080#64) (n := 48) (k := 56)
    (b' := sp + 4128#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
theorem memRegion_4192_504_eq (sp : BitVec 64) :
    memRegion (sp + 4192#64) 504 = memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4640#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4192#64) (n := 448) (k := 56)
    (b' := sp + 4640#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
theorem memRegion_1260_2400_split (sp : BitVec 64) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide) :
    memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
      memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := sz + chunkSize) (k := 2400 - (sz + chunkSize))
    (b' := sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize))
    (by change 2400 = sz + 34 + (2400 - (sz + 34)); have : sz + 34 ≤ 2400 := hsz; omega) rfl (by omega)

omit [LibsignalPlacement] in
private theorem memRegion_7104_24_eq (sp : BitVec 64) :
    memRegion (sp + 7104#64) 24 = memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7120#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x1bc0#64) (n := 16) (k := 8)
    (b' := sp + 7120#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem memRegion_7536_400_eq (sp : BitVec 64) :
    memRegion (sp + 7536#64) 400 = memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 7584#64) 352 :=
  ProofLib.memRegion_split' (b := sp + 0x1d70#64) (n := 48) (k := 352)
    (b' := sp + 7584#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
theorem statesSendPreArmScratch_eq_post (sp : BitVec 64) :
    statesSendPreArmScratch sp =
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗ statesSendPostArmScratch sp := by
  unfold statesSendPreArmScratch statesSendPostArmScratch
  rw [memRegion_7104_24_eq sp, memRegion_7536_400_eq sp]; sep_ac_rfl

def statesSendLeafScratchRest (sp : BitVec 64) (sz : Nat) : SepProp :=
  memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗
  memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4192#64) 504 ∗
  memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) ∗
  memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400

omit [LibsignalPlacement] in
theorem statesSendPreArmScratch_eq_leaf (sp : BitVec 64) (sz : Nat)
    (hsz : sz + chunkSize ≤ 2400 := by decide) :
    statesSendPreArmScratch sp =
      memRegion (sp + 0x1260#64) (sz + chunkSize) ∗ statesSendLeafScratchRest sp sz := by
  unfold statesSendPreArmScratch statesSendLeafScratchRest
  rw [memRegion_1260_2400_split sp sz hsz]; sep_ac_rfl

def statesSendLeafFrame {ctl : BitVec 64} (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (sz : Nat) (Frame : SepProp) : SepProp :=
  spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl cur tape ∗
  optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
  statesSendLeafScratchRest sp sz ∗ Frame

def statesSendImmFrame {ctl : BitVec 64} (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (Frame : SepProp) : SepProp :=
  stackAt sp spqrSendCalleeStack ∗
  tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
  spqrCoinsAtPlaced ctl cur tape ∗ optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
  statesSendPreArmScratch sp ∗ Frame

/-- Non-panicking `SepWP` relocatable continuation contract at `spqrSendPlacedEntry + 3196#64`
    after `<States>::send` and post-arm reassembly. -/
abbrev SpqrSendAt3196SepWPPlaced {F : ShaCompress} {ctl : BitVec 64} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (Env : List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (s0 : State) (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    (msg : Message spqrPolyApi) (st1 : States spqrPolyApi (spqrAuthApi F))
    (tgt : BitVec 64) (Frame : SepProp) (post : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (evs : List AllocEvent),
    Env evs →
    LibsignalCodeRoLoaded lsmpl sf.mem →
    sf.pc = spqrSendPlacedEntry + 3196#64 →
    sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
    sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
    sf.readReg64 .x22 = msg.epoch → sf.readReg64 .x25 = sp + 0x550#64 →
    sf.readReg64 .x26 = sp + 0x1260#64 → sf.readReg64 .x28 = s0.readReg64 .x28 →
    (sf.readReg64 .x23 = noneCap ↔ chain = none) →
    sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    SepWP (spqrSendPlacedProg ext) tgt sf
      ((optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
        memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
        memRegion (sp + 0x950#64) 928 ∗
        optEpochSecretRegSlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
        statesSendPostArmScratch sp ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        spqrLogLevelZeroPlacedAt ∗
        A.pool lim (M.stepEvents evs st_b) sf ∗
        stackAt sp spqrSendCalleeStack) ∗ Frame) post

/-- Panic-aware `SepWPp` relocatable continuation contract at `spqrSendPlacedEntry + 3196#64`
    after `<States>::send` and post-arm reassembly, polymorphic in `panicPost`. -/
abbrev SpqrSendAt3196Placed {F : ShaCompress} {ctl : BitVec 64} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (Env : List AllocEvent → Prop)
    (ext : String → Option (State → State))
    (s0 : State) (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    (msg : Message spqrPolyApi) (st1 : States spqrPolyApi (spqrAuthApi F))
    (ret : BitVec 64) (Frame : SepProp) (post panicPost : State → SepProp → Prop) : Prop :=
  ∀ (sf : State) (evs : List AllocEvent),
    Env evs →
    LibsignalCodeRoLoaded lsmpl sf.mem →
    sf.pc = spqrSendPlacedEntry + 3196#64 →
    sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
    sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
    sf.readReg64 .x22 = msg.epoch → sf.readReg64 .x25 = sp + 0x550#64 →
    sf.readReg64 .x26 = sp + 0x1260#64 → sf.readReg64 .x28 = s0.readReg64 .x28 →
    (sf.readReg64 .x23 = noneCap ↔ chain = none) →
    sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    SepWPp (spqrSendPlacedProg ext) ret sf
      ((optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
        memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
        memRegion (sp + 0x950#64) 928 ∗
        optEpochSecretRegSlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
        statesSendPostArmScratch sp ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        spqrLogLevelZeroPlacedAt ∗
        A.pool lim (M.stepEvents evs st_b) sf ∗
        stackAt sp spqrSendCalleeStack) ∗ Frame) post panicPost

/-- Shared non-panicking `SepWP` continuation from `spqrSendPlacedEntry + 3068#64` to
    `spqrSendPlacedEntry + 3196#64` after any of the 11 arms. -/
theorem step_send_post_arm_cont_sepWP_placed {F : ShaCompress} {ctl : BitVec 64} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (evs : List AllocEvent) (Env : List AllocEvent → Prop) (hevs : Env evs)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {tgt : BitVec 64} {P0 Frame : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hP0 : P0 ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st_b) s1 ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A.repAlloc sp (s1.readReg64 .x21) (s1.readReg64 .x27) key ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
        statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b Env ext s0 sp cur tape tape'
      chain key msg st1 tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s1 P0 post := by
  refine SepWP.weaken_pre hP0 ?_
  rw [statesSendPreArmScratch_eq_post sp]
  refine step_send_post_arm_3068_to_3196_sepWP_placed A lim (M.stepEvents evs st_b) ext hA
    sp chain msg key st1 hvalid hjoin1 hsp_align hinv1
    (Frame := memRegion (sp + 0x950#64) 928 ∗ statesSendPostArmScratch sp ∗
      spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by sep_ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f _ hx22_f hx25_f hx26_f _ hx28_f hx23_none hz_f hvregs_f
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sf evs hevs hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f)

/-- Panic-aware `SepWPp` continuation from `spqrSendPlacedEntry + 3068#64` to
    `spqrSendPlacedEntry + 3196#64` after any of the 11 arms. -/
theorem step_send_post_arm_cont_placed {F : ShaCompress} {ctl : BitVec 64} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (evs : List AllocEvent) (Env : List AllocEvent → Prop) (hevs : Env evs)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {P0 Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hP0 : P0 ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st_b) s1 ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        optChainPBAt A.repAlloc (sp + 0x60#64) chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A.repAlloc sp (s1.readReg64 .x21) (s1.readReg64 .x27) key ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
        statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A lim st_b Env ext s0 sp cur tape tape'
      chain key msg st1 ret Frame post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P0 post panicPost := by
  apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3196#64) hinv1
  refine step_send_post_arm_cont_sepWP_placed A lim st_b evs Env hevs ext hA sp cur tape tape'
    chain key hjoin1 hvalid hsp_align hinv1 hP0 ?_
  intro sf evs' hevs' hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f
  exact SepWP.done hpc_f hrun_f fun _ =>
    hnext sf evs' hevs' hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f

/-- Specialization of `step_send_post_arm_cont_sepWP_placed` for the 6 leaf-call arms
    (`tape' = tape`, `key = none`). -/
theorem step_send_post_arm_cont_leaf_sepWP_placed {F : ShaCompress} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (evs : List AllocEvent) (Env : List AllocEvent → Prop) (hevs : Env evs)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext) {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8))
    (chain : Option ChainPB) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {tgt : BitVec 64} {Frame : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b Env ext s0 sp cur tape tape
      chain none msg st1 tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s1
      ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st_b) s1 ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A.repAlloc sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1) ∗
       statesSendLeafFrame (ctl := ctl) A.repAlloc sp cur tape chain sz Frame) post := by
  refine step_send_post_arm_cont_sepWP_placed (ctl := ctl) A lim st_b evs Env hevs ext hA
    sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendLeafFrame; rw [statesSendPreArmScratch_eq_leaf sp sz hsz]
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spqrCoinsAtPlaced_entails_after_same _ _ _))))
    (Entails.of_eq (by sep_ac_rfl))

/-- Specialization of `step_send_post_arm_cont_sepWP_placed` for the 3 immediate arms
    (`tape' = tape`, `key = none`, `evs = []`). -/
theorem step_send_post_arm_cont_imm_sepWP_placed {F : ShaCompress} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (Env : List AllocEvent → Prop) (hevs : Env [])
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8))
    (chain : Option ChainPB)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {tgt : BitVec 64} {Frame : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hnext : SpqrSendAt3196SepWPPlaced (ctl := ctl) A lim st_b Env ext s0 sp cur tape tape
      chain none msg st1 tgt Frame post) :
    SepWP (spqrSendPlacedProg ext) tgt s1
      ((memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A.repAlloc sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A.repAlloc (sp + 0x590#64) st1 ∗
        A.pool lim st_b s1) ∗
       statesSendImmFrame (ctl := ctl) A.repAlloc sp cur tape chain Frame) post := by
  refine step_send_post_arm_cont_sepWP_placed (ctl := ctl) A lim st_b [] Env hevs ext hA
    sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendImmFrame
  change _ ⊢ (_ ∗ A.pool lim st_b s1 ∗ _) ∗ Frame
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (spqrCoinsAtPlaced_entails_after_same _ _ _)))))))
    (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendDispatchPlacedBudgetAux
