/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopRegions
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Top
import LibsignalBinary.Proofs.SpqrV1.Top.Send.TopPhase3
import ProofLib.SepLogic.WPp

@[expose] public section

/-!
# Budget-Threaded Relocatable Phase 3 & 4 Composition (`+3196 -> s0.x30`, Block `427`)

Threads `RustCliAllocBudget` through Phase 3b–3e, Phase 4 `PqRatchetState` drop cleanup,
and the shared return epilogue (`+3196 -> s0.x30`) for `spqr::send::<signal_session_ratchet::Coins>`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Top.DecodeState (vecU8Heap)
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawChain)
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced
open CryptoVerification.Cli.SpqrV1.ProtoRepr
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.States1aPlacedBudget (dropChunkedStatesLocal1PlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget (etvMemcpyRegionSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs StatesIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget (statesIntoPbPlacedSpecX statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (MessageSerializeEnv messageSerializeSpecX messageSerializeSpecXOfEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge1PlacedBudgetAux
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesBridge2PlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesChainPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish1PlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinish2PlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.AfterStatesFinishPlacedBudget
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopRegionsPlacedBudget

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] ite_zero32_self ite_zero64_self

/-! ## 1. Outcome-Polymorphic `SepWPp` Helpers -/

/-- Lift a non-panicking, non-OOM `SepWP` return proof into `SepWPp` for arbitrary `post`, `Qp`,
    and `oom`. -/
theorem sepWPp_of_early_return_oom {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hwp : SepWP prog ret s P Q)
    (hpost : ∀ sf Pf, sf.pc = ret → sf.status = .Running → Q sf Pf → post sf Pf) :
    SepWPp prog ret s P post Qp oom := by
  intro R hm hL
  rcases hwp.elim hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq⟩ | ⟨_, hfalse⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hpost sf Pf hpc hrun hq⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Frame-drop a left-hand `SepProp` inside `SepWPp` for arbitrary `Q`, `Qp`, and `oom`. -/
theorem sepWPp_drop_left_oom {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (Drop ∗ P) Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) hL

/-- Introduce `CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt` from `LibsignalRoLoaded lsmpl s.mem` inside
    outcome-polymorphic `SepWPp`. -/
theorem sepWPp_intro_chunkedStatesLocal1JumpTable_oom_placed
    {prog : Program} {ret : BitVec 64} {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s (CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R0 hm hL
  have hm' : s.mem ⊨ (CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact CryptoVerification.Cli.SpqrV1.Top.Send.lsro_chunkedStatesLocal1JumpTablePlacedAt hro hm
  exact h R0 hm' hL

/-! ## 2. Phase 4 Finish + Epilogue (`+6216 -> s0.readReg64 .x30`) -/

/-- Budget-threaded relocatable Phase 4 finish + epilogue composition
    (`spqrSendPlacedEntry + 6216#64 -> s0.readReg64 .x30`), polymorphic in `post`, `Qp`, and
    `oom` (zero panics, zero OOMs, `FreeOnlyEvs` allocator events). -/
theorem step_send_from_320a4_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExtPlaced M A lim ext)
    (s0 sm : State) (bst : M.σ) (sp ret v_20 x21 x23 x25 x27 w0 w16 : BitVec 64)
    (stBytes msgBytes : Bytes) (salt : CryptoGames.HKDF.Salt)
    (g : PqRatchetStatePBGhost) (pq' : PqRatchetState) (Rest : SepProp)
    {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : LibsignalCodeLoaded lsmpl sm.mem)
    (hmsg_len : msgBytes.length < 2 ^ 32) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : sm.pc = spqrSendPlacedEntry + 6216#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx23 : sm.readReg64 .x23 = x23) (hx25 : sm.readReg64 .x25 = x25)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 4192#64)
    (hflag : x21 = noneCap ∨ BitVec.truncate 32 v_20 = 0#32)
    (hx25_ch : (x25 + 1#64 == 0#64) = !pq'.chain.isSome)
    (hpost : ∀ (evs : List AllocEvent), FreeOnlyEvs evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret (some (stBytes, salt, msgBytes)) ∗
          A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s0.sp spqrSendStack ∗
          spqrSendDropJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
      (memRegion ret 72 ∗ vecU8 A.repAlloc (sp + 1424#64) stBytes ∗
        vecU8 A.repAlloc (sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A.repAlloc sp salt ∗ ((sp + 32#64) ↦₆₄ v_20) ∗
        (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ w16) ∗
        memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 ∗
        pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
        memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗
        spqrSendDropJumpTablePlacedAt ∗ A.pool lim bst sm ∗ stackAt sp spqrSendCalleeStack ∗ Rest)
      post Qp oom := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hfin := TopRegionsPlacedBudget.step_send_finish_320a4'_placed hdealloc sm bst ret v_20 x21 x23 x25 x27
    stBytes msgBytes salt g pq'
    ((sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ w16) ∗
      memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
      memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 5056#64) 576 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ Rest)
    hcl hmsg_len hpc hrun hx19 hx21 hx23 hx25 hx27 (by rw [hsp]; exact hx28) hflag hx25_ch hsp_align
  rw [hsp] at hfin
  refine sepWPp_of_early_return_oom
    (Q := fun sf Pf => ∃ evs : List AllocEvent, FreeOnlyEvs evs ∧
      (Pf ⊢ spqrSendResultAt A.repAlloc ret (some (stBytes, salt, msgBytes)) ∗
        A.pool lim (M.stepEvents evs bst) sf ∗ stackAt s0.sp spqrSendStack ∗
        spqrSendDropJumpTablePlacedAt ∗ Rest) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
    (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWP.seq hfin fun s1 Q1 hpc1 _ ⟨evs, hevs, _, hrun1, htr1, hsp1, hx23_1, hvregs1, hQ1⟩ => ?_))
    fun sf Pf hpcf hrunf ⟨evs, hevs, hPf, hspf, hcsf, htrf⟩ =>
      hpost evs hevs sf Pf hpcf hrunf hPf hspf hcsf htrf
  have hsp1' : s1.sp = sp := hsp1
  have hjoin : Q1 ⊢
      memRegion s1.sp 0x60 ∗ chainOrigSlotAt s1.sp x23 ∗ memRegion (s1.sp + 0xb0#64) (0x1f20 - 0xb0) ∗
      stackAt s1.sp spqrSendCalleeStack ∗ spqrSendSavedRegs s1.sp s0 ∗
      (spqrSendResultAt A.repAlloc ret (some (stBytes, salt, msgBytes)) ∗
       spqrSendDropJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs bst) s1 ∗ Rest) := by
    rw [hsp1', memRegion_b0_1f20_eq_finish sp]
    refine Entails.trans hQ1 ?_
    refine Entails.trans (Entails.of_eq (show _ =
      ((sp ↦₆₄ w0) ∗ memRegion (sp + 8#64) 8 ∗ ((sp + 16#64) ↦₆₄ w16) ∗
        memRegion (sp + 24#64) 24 ∗ memRegion (sp + 0x30#64) 48) ∗
      (chainOrigSlotAt sp x23 ∗
        (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1424#64) 24 ∗
         memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
         memRegion (sp + 0x950#64) 928 ∗
         memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 4192#64) 48 ∗
         memRegion (sp + 4240#64) 32 ∗ memRegion (sp + 4704#64) 352 ∗
         memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
         memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
         stackRestCF0_1F20 sp) ∗
        stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A.repAlloc ret (some (stBytes, salt, msgBytes)) ∗
         spqrSendDropJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs bst) s1 ∗ Rest)) by sep_ac_rfl)) ?_
    exact sepConj_mono_left (memRegion_0_60_join sp w0 w16)
  refine SepWP.weaken_pre hjoin
    (SepWP.mono (AfterStatesBridge1PlacedBudget.step_epilogue_from_31a54_placed s0 s1 x23
      (spqrSendResultAt A.repAlloc ret (some (stBytes, salt, msgBytes)) ∗
       spqrSendDropJumpTablePlacedAt ∗ A.pool lim (M.stepEvents evs bst) s1 ∗ Rest)
      hpc1 hrun1 (hsp1'.trans hsp_eq) hx23_1 hsp0_align (hvregs1.trans hvregs)) ?_)
  intro sf Qf _ _ ⟨hvmf, _, htrf, hspf, hcsf, hQf⟩
  refine ⟨evs, hevs, ?_, hspf, hcsf, (htrf.trans htr1).trans htr⟩
  rw [A.pool_of_vmPreserved hvmf]
  exact Entails.trans hQf (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Phase 3d–4 Envelopes & Composition (`+4000 -> s0.readReg64 .x30`) -/

/-- Right-associated envelope-parametric allocation envelope across Phase 3d–4
    (`+4000 -> s0.readReg64 .x30`), matching `SpqrSendPartsTightGenEnv`'s
    `SeqEnv Emsg (SeqEnv Esinto (SeqEnv Epq FreeOnlyEvs))` tail directly:
    1. `<Message>::serialize` (`MsgSerEnv`),
    2. `<States>::into_pb` (`IntoPbEnv`),
    3. `PqRatchetState::encode_to_vec` (`rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1`),
    4. Phase 4 finish & epilogue (`FreeOnlyEvs`). -/
def SendFrom317fcEnvOfEnv {F : ShaCompress}
    (MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (sp : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }
  SeqEnv
    (MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg })
    (SeqEnv
      (IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 })
      (SeqEnv
        (fun evs => evs = rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1)
        FreeOnlyEvs))

/-- Default right-associated allocation envelope across Phase 3d–4 (`+4000 -> s0.readReg64 .x30`),
    instantiating `MessageSerializeEnv (P := spqrPolyApi)` and `StatesIntoPbEnv`. -/
def SendFrom317fcEnv {F : ShaCompress}
    (idx : BitVec 32) (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    List AllocEvent → Prop :=
  let pq' : PqRatchetState :=
    { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }
  SeqEnv
    (MessageSerializeEnv (P := spqrPolyApi)
      { msgA := 0#64, index := idx, ret := 0#64, msg := msg })
    (SeqEnv
      (StatesIntoPbEnv { out := 0#64, stA := 0#64, st := st1 })
      (SeqEnv
        (fun evs => evs = rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1)
        FreeOnlyEvs))

omit [LibsignalPlacement] in
theorem sendFrom317fcEnv_eq_ofEnv {F : ShaCompress}
    (sp : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendFrom317fcEnv idx vn chainPb st1 msg =
      SendFrom317fcEnvOfEnv (MessageSerializeEnv (P := spqrPolyApi)) StatesIntoPbEnv
        sp idx vn chainPb st1 msg :=
  rfl

omit [LibsignalPlacement] in
theorem sendFrom317fcEnvOfEnv_intro {F : ShaCompress}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {sp : BitVec 64} {idx : BitVec 32}
    {vn : Option VersionNegotiationPB} {chainPb : Option ChainPB}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {evs₁ evs₂ evs₄ : List AllocEvent}
    (hmser : MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } evs₁)
    (hinto : IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } evs₂)
    (hfree : FreeOnlyEvs evs₄) :
    SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg
      (evs₁ ++ (evs₂ ++ (rustAllocEvents
        (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }) 1 ++ evs₄))) :=
  SeqEnv.append hmser (SeqEnv.append hinto (SeqEnv.append rfl hfree))

omit [LibsignalPlacement] in
theorem sendFrom317fcEnv_nonempty {F : ShaCompress}
    (idx : BitVec 32) (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendFrom317fcEnv idx vn chainPb st1 msg
      (([] : List AllocEvent) ++
        ([] ++ (rustAllocEvents
          (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }) 1 ++ []))) :=
  SeqEnv.append (SpqrBoundedEvs.nil 8 256)
    (SeqEnv.append ⟨Nat.zero_le _, fun _ h => nomatch h⟩ (SeqEnv.append rfl FreeOnlyEvs.nil))

omit [LibsignalPlacement] in
theorem fitsEnv_sendBridge2EnvOfEnv_of_sendFrom317fcEnvOfEnv
    {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ} {F : ShaCompress}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {sp : BitVec 64} {idx : BitVec 32}
    {vn : Option VersionNegotiationPB} {chainPb : Option ChainPB}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    (h : FitsEnv M lim st0 (SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg)) :
    FitsEnv M lim st0 (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg) :=
  fitsEnv_sendBridge2EnvOfEnv_of_seq_tail h

/-- Envelope-parametric Phase 3d–4 composition (`spqrSendPlacedEntry + 4000#64 -> s0.readReg64 .x30`),
    exposing the individual per-phase event lists `evs₁`, `evs₂`,
    `evs₃ := rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1`, and `evs₄` (`FreeOnlyEvs evs₄`),
    under `FitsEnv M lim st0 (SendBridge2EnvOfEnv ...)`, polymorphic in `post`, `Qp`, and `oom`. -/
theorem step_send_from_317fc_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hinto : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    (s0 s : State) (sp ret x23 : BitVec 64)
    (idx : BitVec 32) (msgKey : Bytes) (hmk_cases : msgKey = [] ∨ msgKey.length = 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg))
    (Rest : SepProp) {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hsp : s.sp = sp)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 msgKey.length)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg32 .x24 = idx)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32)
    (hpost : ∀ (salt : CryptoGames.HKDF.Salt) (evs₁ evs₂ evs₄ : List AllocEvent),
      let pq' : PqRatchetState :=
        { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }
      let evs₃ : List AllocEvent := rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } evs₁ →
      IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } evs₂ →
      FreeOnlyEvs evs₄ →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw pq', salt, msg.serialize idx)) ∗
          A.pool lim (M.stepEvents (evs₁ ++ (evs₂ ++ (evs₃ ++ evs₄))) st0) sf ∗
          stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ A.pool lim st0 s ∗
        stackAt sp spqrSendCalleeStack ∗
        chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
      post Qp oom := by
  have hsp_align : sp &&& 15#64 = 0#64 := by
    rw [hsp_eq]; exact beq_iff_eq.mp (ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide))
  obtain ⟨salt, hsalt_eq, hsalt_ent⟩ := msgKey_to_optMsgKeySlotsAt A.repAlloc sp msgKey hmk_cases
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
    (memRegion sp 8 ∗ memRegion (sp + 16#64) 24) ∗
    (optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
      (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
      chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ A.pool lim st0 s ∗
      stackAt sp spqrSendCalleeStack ∗
      chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
      memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
      memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
      memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
      messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
      spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) by sep_ac_rfl)) ?_
  rw [memRegion_sp_0_16_24_words sp]
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_20_old
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp18
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v_sp10
  rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro v0
  refine AfterStatesBridge2PlacedBudget.step_send_bridge2_317fc_ofEnv_placed st0 hA hmser hinto (s0 := s) hinv
    sp v_20_old v0 v_sp10 v_sp18 idx vn chainPb st1 msg hlen hFit hsp_align
    (Frame := (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
        ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
      memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
      memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
      memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
      stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
    hpc hrun hsp rfl hx24 hx26 hx28 ⟨fun _ h => h, rfl, rfl⟩
    (by rw [memRegion_590_224_eq_88_136 sp, memRegion_1260_928_eq_88_840 sp]; sep_ac_rfl) ?_
  intro sm evs₁ evs₂ g w0_new pq' evs₃ hmser1 hinto2 hpc_m hrun_m hsp_m htr_m
    hx19_m hx21_m hx23_m _ hx25_ch hx27_m hx28_m hinv_m hinvm_lscro
  have hdrop :
      ((pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
        vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
        vecU8 A.repAlloc (sp + 4080#64) (msg.serialize idx) ∗
        ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
        (sp ↦₆₄ w0_new) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
        ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
        memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        ((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents (evs₁ ++ (evs₂ ++ evs₃)) st0) sm ∗
        stackAt sp spqrSendCalleeStack) ∗
       ((∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗ chainOrigSlotAt sp x23 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)) =
      (((lsρ cliV1StateJtSym) ↦ᵣ v1StateJumpTableBytes) ∗
        ((lsρ spqrSendRoSym + 22#64) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
        CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt) ∗
      ((((sp + 24#64) ↦₆₄ BitVec.ofNat 64 msgKey.length) ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey)) ∗
       (memRegion ret 72 ∗
        vecU8 A.repAlloc (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
        vecU8 A.repAlloc (sp + 4080#64) (msg.serialize idx) ∗
        ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
        (sp ↦₆₄ w0_new) ∗ ((sp + 16#64) ↦₆₄ optChainCap g.chain pq'.chain) ∗
        memRegion (sp + 0x30#64) 48 ∗ chainOrigSlotAt sp x23 ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 32 ∗
        pqRatchetStatePBPinnedAt A.repAlloc g (sp + 4704#64) pq' ∗
        memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion (sp + 7136#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗
        stackRestCF0_1F20 sp ∗ spqrSendSavedRegs sp s0 ∗
        spqrSendDropJumpTablePlacedAt ∗
        A.pool lim (M.stepEvents (evs₁ ++ (evs₂ ++ evs₃)) st0) sm ∗
        stackAt sp spqrSendCalleeStack ∗ Rest)) := by
    rw [hx22, memRegion_1060_80_eq_48_32 sp]; sep_ac_rfl
  rw [hdrop]
  apply sepWPp_drop_left_oom
  refine SepWPp.weaken_pre (Entails.trans (sepConj_mono_left hsalt_ent) (Entails.of_eq (by sep_ac_rfl)))
    (TopPhase3PlacedBudget.step_send_from_320a4_placed hA.dealloc s0 sm (M.stepEvents (evs₁ ++ (evs₂ ++ evs₃)) st0)
      sp ret (s.readReg64 .x20) (s.readReg64 .x21) x23 (sm.readReg64 .x25) (s.readReg64 .x27)
      w0_new (optChainCap g.chain pq'.chain)
      (PqRatchetState.encodeRaw pq') (msg.serialize idx) salt g pq' Rest
      hinvm_lscro.1 (message_serialize_len_lt_2_32 msg idx) hsp0_align hsp_eq hpc_m hrun_m hsp_m
      (htr_m.trans htr) (hx19_m.trans hx19) hx21_m (hx23_m.trans hx23) rfl hx27_m hx28_m hflag
      hx25_ch
      (fun evs₄ hfree4 sf Pf hpc_f hrun_f hPf hsp_f hcs_f htr_f => by
        have hst_eq :
            M.stepEvents evs₄ (M.stepEvents (evs₁ ++ (evs₂ ++ evs₃)) st0) =
              M.stepEvents (evs₁ ++ (evs₂ ++ (evs₃ ++ evs₄))) st0 := by
          simp only [M.stepEvents_append, List.append_assoc]
        rw [hst_eq] at hPf
        exact hpost salt evs₁ evs₂ evs₄ hsalt_eq hmser1 hinto2 hfree4 sf Pf hpc_f hrun_f
          hPf hsp_f hcs_f htr_f)
      (hinv_m.2.2.trans hvregs))

/-- Single-`evs` wrapper around `step_send_from_317fc_ofEnv_placed`, packaging
    `SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg evs` under
    `FitsEnv M lim st0 (SendFrom317fcEnvOfEnv ...)`. -/
theorem step_send_from_317fc_single_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hinto : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    (s0 s : State) (sp ret x23 : BitVec 64)
    (idx : BitVec 32) (msgKey : Bytes) (hmk_cases : msgKey = [] ∨ msgKey.length = 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg))
    (Rest : SepProp) {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hsp : s.sp = sp)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 msgKey.length)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg32 .x24 = idx)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32)
    (hpost : ∀ (salt : CryptoGames.HKDF.Salt) (evs : List AllocEvent),
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx vn chainPb st1 msg evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) },
                   salt, msg.serialize idx)) ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ A.pool lim st0 s ∗
        stackAt sp spqrSendCalleeStack ∗
        chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
      post Qp oom :=
  TopPhase3PlacedBudget.step_send_from_317fc_ofEnv_placed st0 hA hmser hinto s0 s sp ret x23 idx msgKey hmk_cases
    vn chainPb st1 msg hlen (fitsEnv_sendBridge2EnvOfEnv_of_sendFrom317fcEnvOfEnv hFit) Rest
    hsp0_align hsp_eq hpc hrun htr hsp hinv hx19 hx22 hx23 hx24 hx26 hx28 hflag
    (fun salt evs₁ evs₂ evs₄ hsalt hmser1 hinto2 hfree4 =>
      hpost salt
        (evs₁ ++ (evs₂ ++ (rustAllocEvents
          (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) }) 1 ++ evs₄)))
        hsalt (sendFrom317fcEnvOfEnv_intro hmser1 hinto2 hfree4))
    hvregs

/-- Default Phase 3d–4 composition (`spqrSendPlacedEntry + 4000#64 -> s0.readReg64 .x30`) against
    `messageSerializeSpecX`, `statesIntoPbPlacedSpecX`, and `SendFrom317fcEnv`. -/
theorem step_send_from_317fc_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hmser : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)))
    (hinto : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F)))
    (s0 s : State) (sp ret x23 : BitVec 64)
    (idx : BitVec 32) (msgKey : Bytes) (hmk_cases : msgKey = [] ∨ msgKey.length = 32)
    (vn : Option VersionNegotiationPB) (chainPb : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (hFit : FitsEnv M lim st0 (SendFrom317fcEnv idx vn chainPb st1 msg))
    (Rest : SepProp) {post Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hpc : s.pc = spqrSendPlacedEntry + 4000#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hsp : s.sp = sp)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 msgKey.length)
    (hx23 : s.readReg64 .x23 = x23) (hx24 : s.readReg32 .x24 = idx)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x20 = 0#32)
    (hpost : ∀ (salt : CryptoGames.HKDF.Salt) (evs : List AllocEvent),
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      SendFrom317fcEnv idx vn chainPb st1 msg evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := vn, chain := chainPb, inner := some (.v1 st1.into_pb) },
                   salt, msg.serialize idx)) ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗ spqrSendDropJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) st1 ∗ A.pool lim st0 s ∗
        stackAt sp spqrSendCalleeStack ∗
        chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) vn ∗
        memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
        memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗ Rest)
      post Qp oom :=
  TopPhase3PlacedBudget.step_send_from_317fc_single_ofEnv_placed st0 hA hmser hinto s0 s sp ret x23 idx msgKey
    hmk_cases vn chainPb st1 msg hlen hFit Rest hsp0_align hsp_eq hpc hrun htr hsp hinv
    hx19 hx22 hx23 hx24 hx26 hx28 hflag hpost hvregs

/-! ## Phase 3–4 Full Envelopes & Composition (`+3196 -> s0.readReg64 .x30`) -/

/-- Envelope-parametric allocation envelope across Phase 3 & 4
    (`spqrSendPlacedEntry + 3196#64 -> s0.readReg64 .x30`), with zero existential binders:
    - `.ok (idx, _, chainPb)`: `SeqEnv (SendChainPhaseEnv ...) (SendFrom317fcEnvOfEnv ...)`,
    - `.error (.err _)`: `SeqEnv (SendChainPhaseEnv ...) FreeOnlyEvs` (including `vn` drop at `+4576`),
    - `.error (.panic _)`: `SendChainPhaseEnv ...`. -/
def SendPhase3EnvOfEnv {F : ShaCompress}
    (MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop)
    (IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop)
    (sp : BitVec 64) (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  match sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
  | .ok (idx, _, chainPb) =>
    SeqEnv
      (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch)
      (SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx pq.versionNegotiation chainPb sOut.state sOut.msg)
      evs
  | .error (.err _) =>
    SeqEnv
      (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch)
      FreeOnlyEvs
      evs
  | .error (.panic _) =>
    SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch evs

/-- Default allocation envelope across Phase 3 & 4 (`spqrSendPlacedEntry + 3196#64 -> s0.readReg64 .x30`),
    instantiating `MessageSerializeEnv spqrPolyApi` and `StatesIntoPbEnv`. -/
def SendPhase3Env {F : ShaCompress}
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (evs : List AllocEvent) : Prop :=
  match sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
  | .ok (idx, _, chainPb) =>
    SeqEnv
      (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch)
      (SendFrom317fcEnv idx pq.versionNegotiation chainPb sOut.state sOut.msg)
      evs
  | .error (.err _) =>
    SeqEnv
      (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch)
      FreeOnlyEvs
      evs
  | .error (.panic _) =>
    SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch evs

omit [LibsignalPlacement] in
theorem sendPhase3Env_eq_ofEnv {F : ShaCompress}
    (sp : BitVec 64) (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    SendPhase3Env pq sOut =
      SendPhase3EnvOfEnv (MessageSerializeEnv (P := spqrPolyApi)) StatesIntoPbEnv sp pq sOut :=
  rfl

omit [LibsignalPlacement] in
theorem sendPhase3Env_chain_vn_none_nil {F : ShaCompress}
    (inner : Option PqRatchetState.Inner)
    (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    SendPhase3Env { versionNegotiation := none, chain := none, inner := inner } sOut [] := by
  unfold SendPhase3Env
  have hch : sendChainPhase (spqrHkdfWith F) none none sOut.key sOut.msg.epoch =
      .error (.err .chainNotAvailable) := rfl
  rw [hch]
  exact Or.inl FreeOnlyEvs.nil

omit [LibsignalPlacement] in
theorem sendPhase3Env_vn_le_zero_nonempty {F : ShaCompress}
    (v : VersionNegotiationPB) (hle : BitVec.slt 0#32 v.minVersion = false)
    (inner : Option PqRatchetState.Inner)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendPhase3Env
      { versionNegotiation := some v, chain := none, inner := inner }
      { state := st1, msg := msg, key := none }
      (([] : List AllocEvent) ++
        ([] ++ (rustAllocEvents
          (pqRatchetStatePBEncodedLen { versionNegotiation := some v, chain := none, inner := some (.v1 st1.into_pb) }) 1 ++ []))) := by
  unfold SendPhase3Env
  have hch : sendChainPhase (spqrHkdfWith F) none (some v) none msg.epoch = .ok (0#32, [], none) := by
    unfold sendChainPhase CryptoVerification.SpqrV1.Top.Send.sendResolveChain
      CryptoVerification.SpqrV1.Top.Send.sendStepChain
    simp [CryptoVerification.LibsignalSpqrV1.Version.toI32, hle]; rfl
  rw [hch]
  have h1 : SendChainPhaseEnv (spqrHkdfWith F) none (some v) none msg.epoch [] := by
    unfold SendChainPhaseEnv AfterStatesBridge1PlacedBudgetAux.SendStepChainEnv
    simp [hle]
  exact SeqEnv.append h1 (sendFrom317fcEnv_nonempty 0#32 (some v) none st1 msg)

/-- Structured envelope-parametric Phase 3 & 4 composition
    (`spqrSendPlacedEntry + 3196#64 -> s0.readReg64 .x30`), exposing per-phase event lists
    (`(evs_ch, evs_ep)` on `.error (.err _)` and `(evs_ch, evs₁, evs₂, evs₄)` on `.ok`) for direct
    `SpqrSendPartsTightGenEnv` composition in `TopPlacedBudget`. -/
theorem step_send_from_314d8_split_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {φ_panic : State → Prop}
    {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hpanic : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked)
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hfrom_vn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith F) M A lim)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) M A lim)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith F) M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (hser_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hstates_into_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    (s0 sm : State) (sp ret x21 x27 x23 : BitVec 64)
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hFit : FitsEnv M lim st0 (SendPhase3EnvOfEnv MsgSerEnv IntoPbEnv sp pq sOut))
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54)
    (hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63)
    (hinv : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc : sm.pc = spqrSendPlacedEntry + 3196#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx22 : sm.readReg64 .x22 = sOut.msg.epoch) (hx23 : sm.readReg64 .x23 = x23)
    (hx25 : sm.readReg64 .x25 = sp + 0x550#64) (hx26 : sm.readReg64 .x26 = sp + 0x1260#64)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 0x1060#64)
    (hx23_none : x23 = noneCap ↔ pq.chain = none)
    (hpstate : sm.pstate = addsPState64 x23 1#64)
    (hφ : ∀ sf : State,
      (sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true ∧
        sf.trace = s0.trace → φ_panic sf)
    (herr_post : ∀ (err : Error) (evs_ch evs_ep : List AllocEvent),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err) →
      SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch evs_ch →
      FreeOnlyEvs evs_ep →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents (evs_ch ++ evs_ep) st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_post : ∀ (idx : BitVec 32) (msgKey : Bytes) (chainPb : Option ChainPB)
        (salt : CryptoGames.HKDF.Salt) (evs_ch evs₁ evs₂ evs₄ : List AllocEvent),
      let pq' : PqRatchetState :=
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) }
      let evs₃ : List AllocEvent := rustAllocEvents (pqRatchetStatePBEncodedLen pq') 1
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb) →
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch evs_ch →
      MsgSerEnv { msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := sOut.msg } evs₁ →
      IntoPbEnv { out := sp + 0x590#64, stA := sp + 0x1260#64, st := sOut.state } evs₂ →
      FreeOnlyEvs evs₄ →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw pq', salt, sOut.msg.serialize idx)) ∗
          A.pool lim (M.stepEvents (evs_ch ++ (evs₁ ++ (evs₂ ++ (evs₃ ++ evs₄)))) st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
      (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A.repAlloc sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        A.pool lim st0 sm ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_align : (sm.sp &&& 15#64 == 0#64) = true := by
    rw [hsp, hsp_eq]; exact ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc := AfterStatesFinish1PlacedBudget.spqrSend_dealloc_sub_ok_placed hA.dealloc
  have hFit_chain : FitsEnv M lim st0
      (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch) := by
    refine hFit.mono fun evs hevs => ?_
    unfold SendPhase3EnvOfEnv
    cases sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch with
    | ok _ => exact Or.inl hevs
    | error e =>
      cases e with
      | err _ => exact Or.inl hevs
      | panic _ => exact hevs
  apply sepWPp_intro_chunkedStatesLocal1JumpTable_oom_placed hinv.2
  let Frame314d8 : SepProp :=
    memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
    memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
    memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
    memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
    messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
    spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
    (spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
  have hres := AfterStatesBridge1PlacedBudget.step_chain_resolve_314d8_to_7fc_placed (spqrHkdfWith F) hpanic hpanic_sub hdealloc
    hdrop_slice hdrop_states hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb
    s0 sm st0 ret x21 x27 x23 pq.chain hchain_raw pq.versionNegotiation sOut.key sOut.msg.epoch
    sOut.state Frame314d8 Fr φ_panic hFit_chain hinv hpc hrun htr hx23_none hpstate
    hx19 hx21 hx22 hx23 (by rw [hsp]; exact hx25) (by rw [hsp]; exact hx26)
    hx27 (by rw [hsp]; exact hx28) hsp_align hφ hvregs
  rw [hsp] at hres
  have hpre_eq :
      CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
      (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A.repAlloc sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        A.pool lim st0 sm ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) =
      optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A.repAlloc sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim st0 sm ∗ stackAt sp spqrSendCalleeStack ∗ Frame314d8 := by
    dsimp only [Frame314d8]; sep_ac_rfl
  rw [hpre_eq]
  refine sepWPp_bind hres fun s1 P1 hpc1 hrun1 hpost1 => ?_
  generalize hch : sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = res at hpc1 hpost1
  rcases res with (err | p) | ⟨idx, msgKey, chainPb⟩
  · rcases hpost1 with ⟨evs_ch, hevs_ch, _, htr1, hsp1, hinv1, hx23_1, hvregs1, hQ1⟩
    refine SepWPp.weaken_pre hQ1 ?_
    have hjoin_err :
        spqrSendResultAt A.repAlloc ret none ∗ memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xd90#64) 72 ∗
        memRegion (sp + 0x28#64) 8 ∗ memRegion (sp + 0x8#64) 8 ∗
        memRegion (sp + 0x190#64) 928 ∗ CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_ch st0) s1 ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) ⊢
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        (memRegion sp 0x30 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
         chainOrigSlotAt sp x23 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) ∗
         A.pool lim (M.stepEvents evs_ch st0) s1 ∗
         stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
         (spqrSendResultAt A.repAlloc ret none ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)) := by
      dsimp only [Frame314d8]
      have hmsg := messageAt_entails_memRegion_48 (sp + 0x1d70#64) sOut.msg
      have h0_30 :
          memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8 =
          memRegion sp 0x30 := by
        rw [memRegion_0_30_eq sp,
            ProofLib.memRegion_split' (b := sp + 16#64) (n := 8) (k := 16) (b' := sp + 24#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_split' (b := sp + 24#64) (n := 8) (k := 8) (b' := sp + 32#64) rfl (by bv_omega) (by decide),
            memRegion_32_16_eq_8_8 sp]
        sep_ac_rfl
      have hff0 : (sp + 0xff0#64 : BitVec 64) = sp + 4080#64 := rfl
      rw [hff0]
      refine Entails.trans (Entails.of_eq (show _ =
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗
        (memRegion sp 8 ∗ memRegion (sp + 0x8#64) 8 ∗ memRegion (sp + 16#64) 24 ∗ memRegion (sp + 0x28#64) 8) ∗
        (memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x590#64) 88 ∗
         memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp) ∗
        memRegion (sp + 0x950#64) 928 ∗
        (memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
         memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
         stackRestCF0_1F20 sp) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ A.pool lim (M.stepEvents evs_ch st0) s1 ∗
        stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A.repAlloc ret none ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hmsg) ?_
      rw [h0_30, ← memRegion_b0_950_eq_rest sp]
      refine Entails.trans (Entails.of_eq (show _ =
        memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗ memRegion (sp + 0x950#64) 928 ∗
        (memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
         memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0xde0#64) 80 ∗
         memRegion (sp + 4080#64) 24 ∗ memRegion (sp + 0x1060#64) 80 ∗
         memRegion (sp + 0x1260#64) 88 ∗ memRegion (sp + 4792#64) 840 ∗
         memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7136#64) 16 ∗
         memRegion (sp + 0x1d70#64) 48 ∗ stackRestCF0_1F20 sp) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ A.pool lim (M.stepEvents evs_ch st0) s1 ∗
        stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A.repAlloc ret none ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) by sep_ac_rfl)) ?_
      have hb0_1f20 :
          memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0) =
          memRegion sp 0x30 ∗ memRegion (sp + 0xb0#64) (0x1f20 - 0xb0) := by
        rw [memRegion_b0_1f20_eq sp]
      rw [← memRegion_cf0_1f20_eq_rest sp]
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion sp 48 ∗ memRegion (sp + 0xb0#64) (0x950 - 0xb0) ∗
         memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xcf0#64) (0x1f20 - 0xcf0)) ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        chainOrigSlotAt sp x23 ∗ A.pool lim (M.stepEvents evs_ch st0) s1 ∗
        stackAt sp spqrSendCalleeStack ∗ spqrSendSavedRegs sp s0 ∗
        (spqrSendResultAt A.repAlloc ret none ∗
         spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
         CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) by sep_ac_rfl)) ?_
      rw [hb0_1f20]
      exact Entails.of_eq (by sep_ac_rfl)
    refine SepWPp.weaken_pre hjoin_err ?_
    apply sepWPp_drop_left_oom (Drop := CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt)
    have hep := AfterStatesBridge1PlacedBudget.step_epilogue_from_31a3c_placed hdealloc s0 s1 (M.stepEvents evs_ch st0)
      pq.versionNegotiation x23
      (spqrSendResultAt A.repAlloc ret none ∗
       spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
       CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
      hpc1 hrun1 (hsp1.trans hsp_eq) hx23_1 hsp0_align hvregs1
    rw [hsp1] at hep
    refine sepWPp_of_early_return_oom
      (Q := fun sf Pf => ∃ evs_ep : List AllocEvent, FreeOnlyEvs evs_ep ∧
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents (evs_ch ++ evs_ep) st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace)
      (SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hep ?_))
      fun sf Pf hpcf hrunf ⟨evs_ep, hevs_ep, hPf, hspf, hcsf, htrf⟩ =>
        herr_post err evs_ch evs_ep hch hevs_ch hevs_ep sf Pf hpcf hrunf hPf hspf hcsf htrf
    intro sf Pf _ _ ⟨evs_ep, hevs_ep, _, htr_f, hsp_f, hcs_f, hPf⟩
    rw [← M.stepEvents_append] at hPf
    exact ⟨evs_ep, hevs_ep, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
      hsp_f, hcs_f, htr_f.trans htr1⟩
  · exact False.elim hpost1
  · rcases hpost1 with ⟨evs_ch, hevs_ch, _, htr1, hsp1, hinv1,
      hx19_1, hx22_1, hx23_1, hx24_1, hx26_1, hx28_1, hflag_1, hvregs1, hQ1⟩
    refine SepWPp.weaken_pre hQ1 ?_
    have hdrop_ro :
        optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s1.readReg64 .x25) chainPb ∗
        (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
          ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        A.pool lim (M.stepEvents evs_ch st0) s1 ∗ stackAt sp spqrSendCalleeStack ∗
        (chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗ Frame314d8) =
        CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt ∗
        (optChainPBRegSlotAt A.repAlloc (sp + 0xd90#64) (s1.readReg64 .x25) chainPb ∗
          (∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
            ((sp + 0x28#64) ↦₆₄ mkCap) ∗ ((sp + 0x8#64) ↦₆₄ mkPtr) ∗ vecU8Heap A.repAlloc mkCap mkPtr msgKey) ∗
          memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
          memRegion (sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
          chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
          A.pool lim (M.stepEvents evs_ch st0) s1 ∗ stackAt sp spqrSendCalleeStack ∗
          chainOrigSlotAt sp x23 ∗ optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
          memRegion (sp + 0xcf0#64) 80 ∗ memRegion (sp + 0xd40#64) 80 ∗
          memRegion (sp + 0xde0#64) 80 ∗ memRegion (sp + 0x1bc0#64) 16 ∗
          memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
          memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
          memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
          spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
          (spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)) := by
      dsimp only [Frame314d8]; sep_ac_rfl
    rw [hdrop_ro]
    apply sepWPp_drop_left_oom (Drop := CryptoVerification.Cli.SpqrV1.Drop.chunkedStatesLocal1JumpTablePlacedAt)
    have hmk_cases := sendChainPhase_msgKey_cases F pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    have hch_le := sendChainPhase_raw_le (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch hch
    have hFit_ok : FitsEnv M lim st0
        (SeqEnv
          (SendChainPhaseEnv (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch)
          (SendFrom317fcEnvOfEnv MsgSerEnv IntoPbEnv sp idx pq.versionNegotiation chainPb sOut.state sOut.msg)) :=
      hFit.mono fun evs hevs => by unfold SendPhase3EnvOfEnv; rw [hch]; exact hevs
    have hFit_b2 : FitsEnv M lim (M.stepEvents evs_ch st0)
        (SendBridge2EnvOfEnv MsgSerEnv IntoPbEnv sp idx pq.versionNegotiation chainPb sOut.state sOut.msg) :=
      fitsEnv_sendBridge2EnvOfEnv_of_sendFrom317fcEnvOfEnv (hFit_ok.seq_right hevs_ch)
    exact TopPhase3PlacedBudget.step_send_from_317fc_ofEnv_placed (M.stepEvents evs_ch st0) hA hser_call hstates_into_pb
      s0 s1 sp ret x23 idx msgKey hmk_cases pq.versionNegotiation chainPb sOut.state sOut.msg
      (hpq'_len chainPb hch_le) hFit_b2
      (spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
      hsp0_align hsp_eq hpc1 hrun1 htr1 hsp1 hinv1 hx19_1 hx22_1 hx23_1 hx24_1 hx26_1 hx28_1 hflag_1
      (fun salt evs₁ evs₂ evs₄ hsalt hmser1 hinto2 hfree4 sf Pf hpc_f hrun_f hPf hsp_f hcs_f htr_f => by
        rw [← M.stepEvents_append] at hPf
        exact hok_post idx msgKey chainPb salt evs_ch evs₁ evs₂ evs₄ hch hsalt hevs_ch
          hmser1 hinto2 hfree4 sf Pf hpc_f hrun_f
          (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))) hsp_f hcs_f htr_f)
      hvregs1

/-- Single-`evs` envelope-parametric Phase 3 & 4 composition
    (`spqrSendPlacedEntry + 3196#64 -> s0.readReg64 .x30`), packaging
    `SendPhase3EnvOfEnv MsgSerEnv IntoPbEnv sp pq sOut evs`. -/
theorem step_send_from_314d8_ofEnv_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {φ_panic : State → Prop}
    {ext : String → Option (State → State)}
    {MsgSerEnv : MessageSerializeGhost spqrPolyApi → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (hpanic : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked)
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hfrom_vn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith F) M A lim)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) M A lim)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith F) M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (hser_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecXOfEnv spqrPolyApi M A lim MsgSerEnv)))
    (hstates_into_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim F IntoPbEnv)))
    (s0 sm : State) (sp ret x21 x27 x23 : BitVec 64)
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hFit : FitsEnv M lim st0 (SendPhase3EnvOfEnv MsgSerEnv IntoPbEnv sp pq sOut))
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54)
    (hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63)
    (hinv : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc : sm.pc = spqrSendPlacedEntry + 3196#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx22 : sm.readReg64 .x22 = sOut.msg.epoch) (hx23 : sm.readReg64 .x23 = x23)
    (hx25 : sm.readReg64 .x25 = sp + 0x550#64) (hx26 : sm.readReg64 .x26 = sp + 0x1260#64)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 0x1060#64)
    (hx23_none : x23 = noneCap ↔ pq.chain = none)
    (hpstate : sm.pstate = addsPState64 x23 1#64)
    (hφ : ∀ sf : State,
      (sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true ∧
        sf.trace = s0.trace → φ_panic sf)
    (herr_post : ∀ (err : Error) (evs : List AllocEvent),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err) →
      SendPhase3EnvOfEnv MsgSerEnv IntoPbEnv sp pq sOut evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_post : ∀ (idx : BitVec 32) (msgKey : Bytes) (chainPb : Option ChainPB)
        (salt : CryptoGames.HKDF.Salt) (evs : List AllocEvent),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb) →
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      SendPhase3EnvOfEnv MsgSerEnv IntoPbEnv sp pq sOut evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := pq.versionNegotiation
                      chain := chainPb
                      inner := some (.v1 sOut.state.into_pb) },
                   salt, sOut.msg.serialize idx)) ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
      (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A.repAlloc sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        A.pool lim st0 sm ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) :=
  TopPhase3PlacedBudget.step_send_from_314d8_split_ofEnv_placed st0 hA hpanic hpanic_sub hdrop_slice hdrop_states
    hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb hser_call hstates_into_pb
    s0 sm sp ret x21 x27 x23 pq sOut hFit Rest Fr post hsp0_align hsp_eq hchain_raw hpq'_len
    hinv hpc hrun hsp htr hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx23_none hpstate hφ
    (fun err evs_ch evs_ep hch hevs_ch hevs_ep =>
      herr_post err (evs_ch ++ evs_ep) hch
        (by unfold SendPhase3EnvOfEnv; rw [hch]; exact SeqEnv.append hevs_ch hevs_ep))
    (fun idx msgKey chainPb salt evs_ch evs₁ evs₂ evs₄ hch hsalt hevs_ch hmser1 hinto2 hfree4 =>
      hok_post idx msgKey chainPb salt
        (evs_ch ++ (evs₁ ++ (evs₂ ++ (rustAllocEvents
          (pqRatchetStatePBEncodedLen
            { versionNegotiation := pq.versionNegotiation
              chain := chainPb
              inner := some (.v1 sOut.state.into_pb) }) 1 ++ evs₄))))
        hch hsalt
        (by unfold SendPhase3EnvOfEnv; rw [hch]
            exact SeqEnv.append hevs_ch (sendFrom317fcEnvOfEnv_intro hmser1 hinto2 hfree4)))
    hvregs

/-- Default budget-threaded relocatable Phase 3 & 4 composition
    (`spqrSendPlacedEntry + 3196#64 -> s0.readReg64 .x30`) against `messageSerializeSpecX`,
    `statesIntoPbPlacedSpecX`, and `SendPhase3Env`. -/
theorem step_send_from_314d8_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} (st0 : M.σ)
    {F : ShaCompress} {φ_panic : State → Prop}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpanic : ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked)
    (hpanic_sub : ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_sub_overflow" = some Rust.panicked)
    (hdrop_slice : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 446) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (hdrop_states : subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 443) (withLsCodeLoaded lsmpl (dropChunkedStatesLocal1PlacedSpec M A lim F)))
    (hfrom_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hfrom_vn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith F) M A lim)))
    (hadd_epoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith F) M A lim)))
    (hsend_key : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith F) M A lim)))
    (hinto_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (hser_call : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)))
    (hstates_into_pb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim F)))
    (s0 sm : State) (sp ret x21 x27 x23 : BitVec 64)
    (pq : PqRatchetState) (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hFit : FitsEnv M lim st0 (SendPhase3Env pq sOut))
    (Rest Fr : SepProp) (post : State → SepProp → Prop)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hsp_eq : sp = s0.sp - 0x1f80#64)
    (hchain_raw : optRaw rawChain pq.chain + 296 ≤ 2 ^ 54)
    (hpq'_len : ∀ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain pq.chain + 624 →
      pqRatchetStatePBEncodedLen
        { versionNegotiation := pq.versionNegotiation
          chain := chainPb
          inner := some (.v1 sOut.state.into_pb) } < 2 ^ 63)
    (hinv : LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc : sm.pc = spqrSendPlacedEntry + 3196#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = sp) (htr : sm.trace = s0.trace)
    (hx19 : sm.readReg64 .x19 = ret) (hx21 : sm.readReg64 .x21 = x21)
    (hx22 : sm.readReg64 .x22 = sOut.msg.epoch) (hx23 : sm.readReg64 .x23 = x23)
    (hx25 : sm.readReg64 .x25 = sp + 0x550#64) (hx26 : sm.readReg64 .x26 = sp + 0x1260#64)
    (hx27 : sm.readReg64 .x27 = x27) (hx28 : sm.readReg64 .x28 = sp + 0x1060#64)
    (hx23_none : x23 = noneCap ↔ pq.chain = none)
    (hpstate : sm.pstate = addsPState64 x23 1#64)
    (hφ : ∀ sf : State,
      (sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch).isPanic = true ∧
        sf.trace = s0.trace → φ_panic sf)
    (herr_post : ∀ (err : Error) (evs : List AllocEvent),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .error (.err err) →
      SendPhase3Env pq sOut evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret none ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hok_post : ∀ (idx : BitVec 32) (msgKey : Bytes) (chainPb : Option ChainPB)
        (salt : CryptoGames.HKDF.Salt) (evs : List AllocEvent),
      sendChainPhase (spqrHkdfWith F) pq.chain pq.versionNegotiation sOut.key sOut.msg.epoch = .ok (idx, msgKey, chainPb) →
      messageKeyToSalt? (if msgKey.isEmpty then none else some msgKey) = some salt →
      SendPhase3Env pq sOut evs →
      ∀ sf Pf, sf.pc = s0.readReg64 .x30 → sf.status = .Running →
        (Pf ⊢ spqrSendResultAt A.repAlloc ret
            (some (PqRatchetState.encodeRaw
                    { versionNegotiation := pq.versionNegotiation
                      chain := chainPb
                      inner := some (.v1 sOut.state.into_pb) },
                   salt, sOut.msg.serialize idx)) ∗
          A.pool lim (M.stepEvents evs st0) sf ∗
          stackAt s0.sp spqrSendStack ∗
          spqrSendEncodeJumpTablePlacedAt ∗ spqrSendDropJumpTablePlacedAt ∗
          CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest) →
        sf.sp = s0.sp → CalleeSavedPreserved s0 sf → sf.trace = s0.trace → post sf Pf)
    (hvregs : calleeSavedVRegs sm = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (spqrSendPlacedProg ext) (s0.readReg64 .x30) sm
      (optChainPBAt A.repAlloc (sp + 0x60#64) pq.chain ∗
        optVersionNegotiationPBAt A.repAlloc (sp + 0x30#64) pq.versionNegotiation ∗
        optEpochSecretRegSlotAt A.repAlloc sp x21 x27 sOut.key ∗
        memRegion (sp + 0x590#64) 88 ∗ memRegion (sp + 0x1260#64) 88 ∗
        memRegion (sp + 0x1060#64) 80 ∗ memRegion (sp + 0xcf0#64) 80 ∗
        memRegion (sp + 0xd40#64) 80 ∗ memRegion (sp + 0xde0#64) 80 ∗
        memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 0x28#64) 8 ∗
        memRegion (sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A.repAlloc (sp + 0x190#64) sOut.state ∗
        A.pool lim st0 sm ∗ stackAt sp spqrSendCalleeStack ∗
        memRegion sp 8 ∗ memRegion (sp + 16#64) 24 ∗
        memRegion (sp + 1512#64) 136 ∗ stackRestB0_950 sp ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0xff0#64) 24 ∗
        memRegion (sp + 4792#64) 840 ∗ memRegion (sp + 7136#64) 16 ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) sOut.msg ∗ stackRestCF0_1F20 sp ∗
        spqrSendSavedRegs sp s0 ∗ spqrSendDropJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗ CryptoVerification.SpqrV1.States.IntoPb.statesIntoPbJumpTablePlacedAt ∗ Rest)
      post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_panic sf⌝ ∗ anyHeap) ∗ Fr)) :=
  TopPhase3PlacedBudget.step_send_from_314d8_ofEnv_placed st0 hA hpanic hpanic_sub hdrop_slice hdrop_states
    hfrom_pb hfrom_vn hadd_epoch hsend_key hinto_pb hser_call hstates_into_pb
    s0 sm sp ret x21 x27 x23 pq sOut hFit Rest Fr post hsp0_align hsp_eq hchain_raw hpq'_len
    hinv hpc hrun hsp htr hx19 hx21 hx22 hx23 hx25 hx26 hx27 hx28 hx23_none hpstate hφ
    herr_post hok_post hvregs


omit [LibsignalPlacement] in
example {F : ShaCompress} (sp : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendFrom317fcEnvOfEnv (fun _ e => e = []) (fun _ e => e = []) sp idx vn ch st1 msg
      (rustAllocEvents (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) 1) := by
  exact .inr ⟨[], _, (List.nil_append _).symm, rfl, .inr ⟨[], _, (List.nil_append _).symm, rfl, .inr ⟨_, [], (List.append_nil _).symm, rfl, FreeOnlyEvs.nil⟩⟩⟩

omit [LibsignalPlacement] in
example {F : ShaCompress} (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st : CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (msg : Message spqrPolyApi) :
    SendFrom317fcEnv (F := F) idx vn ch (.keysUnsampled st) msg
      (([] : List AllocEvent) ++
       rustAllocEvents (pqRatchetStatePBEncodedLen { versionNegotiation := vn, chain := ch, inner := some (.v1 (States.keysUnsampled (P := spqrPolyApi) (Au := spqrAuthApi F) st).into_pb) }) 1) := by
  exact .inr ⟨[], _, rfl, SpqrBoundedEvs.nil 8 256, .inr ⟨[], _, (List.nil_append _).symm, .nil _ _, .inr ⟨_, [], (List.append_nil _).symm, rfl, FreeOnlyEvs.nil⟩⟩⟩

omit [LibsignalPlacement] in
example {F : ShaCompress} (sp : BitVec 64)
    (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    SendPhase3EnvOfEnv (fun _ e => e = []) (fun _ e => e = []) sp
      { versionNegotiation := none, chain := none, inner := none } sOut [] := by
  unfold SendPhase3EnvOfEnv
  have hch : sendChainPhase (spqrHkdfWith F) none none sOut.key sOut.msg.epoch =
      .error (.err .chainNotAvailable) := rfl
  rw [hch]
  exact Or.inl FreeOnlyEvs.nil

omit [LibsignalPlacement] in
example {F : ShaCompress}
    (sOut : V1Send spqrPolyApi (spqrAuthApi F)) :
    SendPhase3Env { versionNegotiation := none, chain := none, inner := none } sOut [] := by
  unfold SendPhase3Env
  have hch : sendChainPhase (spqrHkdfWith F) none none sOut.key sOut.msg.epoch =
      .error (.err .chainNotAvailable) := rfl
  rw [hch]
  exact Or.inl FreeOnlyEvs.nil

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPhase3PlacedBudget
