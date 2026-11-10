/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# D3 `MainEntryBudgetFitsCapOf` Closure at `cliBudgetLimits` (`1 GiB`)

Discharges `MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
(ReadFileRuleEnvFixed cliIo.rd) uuidTryParse` across the D3 `main` domains:
1. `PksmTryFromWireSliceEnv`: slice projection of `W8bAssemblyPlacedBudget.PksmTryFromEnv` matching
   the `PhaseCreditSpec` and `PhaseGroupSpec` bounds of `PksmTryFromSliceEnv`.
2. `pqD3ScopedRun` (`CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`) at `cliBudgetLimits` (`1 GiB`).
3. `initD3ScopedRun` (`CliInitD3Inputs ⟨W.C, W.Q⟩`, covering over-cap `ReadFileRuleEnvFixed cliIo.rd`
   reads) at `cliBudgetLimits` (`1 GiB`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs pqRecvInputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliIo inputOf parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost PksmGhost RunSem runAns runRel)
open CryptoVerification.SignalSession.Cli.RunProofs (encDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFits
  (binaryKitW1_fineSpec binaryKitW2_fineSpec binaryKitW3Fixed_fineSpec binaryKitW4FixedCum
   binaryKitW4FixedGrpS binaryKitW4FixedLive binaryKitW4FixedMaxReq binaryKitW4FixedPeak
   binaryKitW4Fixed_fineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs pksmSliceCum pksmSliceLive pksmSliceMaxReq pksmSlicePeak)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (boundedReadFileEnv_overCapSchedule mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (binaryKitRunSlotEnvsFixed mkBinaryKitRealCalleeEnvsFixed realCliDecPkBinaryWideSlotEnvFixed
   realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq d3RecvW4ExtPeak)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (BoundedReadFileEnv boundedReadFileEnv_of_readFileRuleEnv_cliIo)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit (pksmTryFromCapDeltaGrpS)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCapOf domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (CliInitD3Inputs initD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)

/-! ## 1. `ReadFileRuleEnvFixed` → `BoundedReadFileEnv` and `PksmTryFromWireSliceEnv` -/

/-- `ReadFileRuleEnvFixed cliIo.rd` embeds into `BoundedReadFileEnv` (`MainEntryBudgetFitsCapReal`). -/
theorem boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    (files : FsFiles) (path : List (BitVec 8)) (evs : List AllocEvent)
    (h : ReadFileRuleEnvFixed cliIo.rd files path evs) :
    BoundedReadFileEnv evs := by
  rcases h with hok | ⟨_, _, rfl⟩
  · exact boundedReadFileEnv_of_readFileRuleEnv_cliIo files path hok
  · exact boundedReadFileEnv_overCapSchedule

/-- Address-normalized wire slice projection of `W8bAssemblyPlacedBudget.PksmTryFromEnv`. -/
def PksmTryFromWireSliceEnv (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  PksmTryFromEnv ⟨0#64, rest, 0#64⟩

section PksmWireSlicePriv

open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost reserveCap)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (decodeProto)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (IntoBoxedBoundedEnv IntoBoxedOptBoundedEnv SigTryFromBoundedEnv SigTryFromPostEnv
   SigTryFromPostOutPreEnv TryCloneBytesEnv sigTryFromDeltaCum sigTryFromDeltaGrpS
   sigTryFromDeltaLive sigTryFromDeltaPeak sigTryFromMaxReq)
open LibsignalBinary.Proofs.PeakBudget.WirePksmLoopCredit (phaseCreditSpec_protoLoop4_S)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
  (PksmAfterKyberOkEnv PksmKyberErrAllocEnv PksmLoopTailBoundedEnv PksmPostBoundedEnv
   PksmPostSeg4Env PksmTryFromLoopBoundedEnv
   phaseCreditSpec_pksmLoopTail_S phaseCreditSpec_pksmPost_blackbox
   phaseGroupSpec_pksmPost_blackbox pksmDecodedInnerBytes pksmDecodedKyberOpt
   pksmDecodedKyberOpt_length_le pksmInnerGhost pksmTryFromDeltaCum
   pksmTryFromDeltaGrpS pksmTryFromDeltaLive
   pksmTryFromDeltaPeak
   pksmTryFromLoopDeltaGrpS pksmTryFromLoop_phaseGroup pksmTryFromMaxReq)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers (ProtoCaps4 ProtoField4)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (fineCostModel_wireGroupHyps fineCostModel_wireLowInterceptHyps)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmAfterLoopEnv PksmFrom5b4PreEnv PksmFrom684PreEnv PksmFrom830PreEnv PksmFrom864PreEnv
   PksmPostEnv PksmPostPreEnv SigMsgCallEnv)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget (bytesMergeEventsCore)

private theorem freeOnlyEvs_nil_local : FreeOnlyEvs [] := by
  intro _ hm; nomatch hm

private theorem freeOnlyEvs_append_local {a b : List AllocEvent}
    (ha : FreeOnlyEvs a) (hb : FreeOnlyEvs b) : FreeOnlyEvs (a ++ b) := by
  intro ev hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact ha ev h1
  · exact hb ev h2

private theorem seqEnv_mono_local {E₁ E₂ F₁ F₂ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h1 : ∀ x, E₁ x → F₁ x) (h2 : ∀ x, E₂ x → F₂ x) (h : SeqEnv E₁ E₂ evs) :
    SeqEnv F₁ F₂ evs := by
  rcases h with ha | ⟨a, b, rfl, ha, hb⟩
  · exact Or.inl (h1 evs ha)
  · exact Or.inr ⟨a, b, rfl, h1 a ha, h2 b hb⟩

private theorem seqEnv_nil_freeOnly_sub {evs : List AllocEvent}
    (h : SeqEnv (· = []) FreeOnlyEvs evs) : FreeOnlyEvs evs := by
  rcases h with rfl | ⟨_, c, rfl, rfl, hc⟩
  · exact freeOnlyEvs_nil_local
  · simpa using hc

private theorem seqEnv_free_left_right {P Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hSub : ∀ e, SeqEnv P FreeOnlyEvs e → Q e)
    (h : SeqEnv (SeqEnv FreeOnlyEvs P) FreeOnlyEvs evs) :
    SeqEnv FreeOnlyEvs Q evs := by
  rcases h with (hf | ⟨a, b, rfl, ha, hb⟩) | ⟨ab, c, rfl, hab, hc⟩
  · exact Or.inl hf
  · exact Or.inr ⟨a, b, rfl, ha, hSub b (Or.inl hb)⟩
  · rcases hab with ha | ⟨a, b, rfl, ha, hb⟩
    · exact Or.inl (freeOnlyEvs_append_local ha hc)
    · exact Or.inr ⟨a, b ++ c, List.append_assoc a b c, ha,
        hSub (b ++ c) (Or.inr ⟨b, c, rfl, hb, hc⟩)⟩

private theorem seqEnv_push_free_right {E₁ P Q : List AllocEvent → Prop} {evs : List AllocEvent}
    (hFreeQ : ∀ e, FreeOnlyEvs e → Q e)
    (hSub : ∀ e, SeqEnv P FreeOnlyEvs e → Q e)
    (h : SeqEnv (SeqEnv E₁ P) FreeOnlyEvs evs) :
    SeqEnv E₁ Q evs := by
  rcases h with (h1 | ⟨a, b, rfl, h1, hp⟩) | ⟨ab, c, rfl, hab, hc⟩
  · exact Or.inl h1
  · exact Or.inr ⟨a, b, rfl, h1, hSub b (Or.inl hp)⟩
  · rcases hab with h1 | ⟨a, b, rfl, h1, hp⟩
    · exact Or.inr ⟨ab, c, rfl, h1, hFreeQ c hc⟩
    · exact Or.inr ⟨a, b ++ c, List.append_assoc a b c, h1,
        hSub (b ++ c) (Or.inr ⟨b, c, rfl, hp, hc⟩)⟩

private def mapMsgField :
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField →
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromField
  | .rk => .rk | .ct => .ct | .pq => .pq | .ad => .ad

private def mapMsgCaps
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromCaps :=
  ⟨c.rk, c.ct, c.pq, c.ad⟩

private theorem mapMsgCaps_get
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) :
    (mapMsgCaps c).get (mapMsgField f) = c.get f := by
  cases f <;> rfl

private theorem mapMsgCaps_set
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) (v : Nat) :
    mapMsgCaps (c.set f v) = (mapMsgCaps c).set (mapMsgField f) v := by
  cases f <;> rfl

private theorem sigErrTail_concrete_sub_msg {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromErrTailEnv evs) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromErrTailEnv evs := by
  cases h with
  | nil => exact .nil
  | fromOnly => exact .fromOnly
  | fromPush hp => exact .fromPush hp

private theorem sigLoop_concrete_sub_msg {rem : Nat}
    {caps : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromLoopBoundedEnv
      rem caps evs) :
    LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec.SigTryFromLoopBoundedEnv
      rem (mapMsgCaps caps) evs := by
  induction h with
  | done ht =>
    exact .done (sigErrTail_concrete_sub_msg ht)
  | skipStep hlt _ ih =>
    exact .skipStep hlt ih
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm hlen hprog hcap _ ih =>
    rw [← mapMsgCaps_get caps f]
    refine .bytesStep (mapMsgField f) wt bs v rest hm hlen hprog ?_ ?_
    · rw [mapMsgCaps_get]; exact hcap
    · rw [mapMsgCaps_get, ← mapMsgCaps_set]; exact ih

private def mapProtoField4 :
    LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField → ProtoField4
  | .rk => .f0 | .ct => .f1 | .pq => .f2 | .ad => .f3

private def mapProtoCaps4
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps) : ProtoCaps4 :=
  ⟨c.rk, c.ct, c.pq, c.ad⟩

private theorem mapProtoCaps4_get
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) :
    (mapProtoCaps4 c).get (mapProtoField4 f) = c.get f := by
  cases f <;> rfl

private theorem mapProtoCaps4_set
    (c : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps)
    (f : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromField) (v : Nat) :
    mapProtoCaps4 (c.set f v) = (mapProtoCaps4 c).set (mapProtoField4 f) v := by
  cases f <;> rfl

private theorem sigLoop_concrete_sub_pksmLoop {rem : Nat}
    {caps : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromCaps}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget.SigTryFromLoopBoundedEnv
      rem caps evs) :
    PksmTryFromLoopBoundedEnv rem (mapProtoCaps4 caps) evs := by
  induction h with
  | done ht =>
    exact .done (PksmLoopTailBoundedEnv.of_sigTryFromErrTail (sigErrTail_concrete_sub_msg ht))
  | skipStep hlt _ ih =>
    exact .skipStep (Nat.le_of_lt hlt) ih
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm hlen hprog hcap _ ih =>
    rw [← mapProtoCaps4_get caps f]
    refine .bytesStep (mapProtoField4 f) wt bs v rest hm hlen hprog ?_ ?_
    · rw [mapProtoCaps4_get]
      exact Nat.lt_trans hcap (by decide : 2 ^ 63 < 2 ^ 64)
    · rw [mapProtoCaps4_get, ← mapProtoCaps4_set]
      exact ih

private theorem intoBoxed_concrete_sub_msg {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedBoundedEnv bs evs) :
    IntoBoxedBoundedEnv bs evs := by
  rcases h with ⟨cap, h1, h2, rfl⟩
  exact ⟨cap, h1, h2, rfl⟩

private theorem intoBoxedOpt_concrete_sub_msg {opt : Option (List (BitVec 8))}
    {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.IntoBoxedOptBoundedEnv
      opt evs) :
    IntoBoxedOptBoundedEnv opt evs := by
  cases opt with
  | none => exact h
  | some ad => exact intoBoxed_concrete_sub_msg h

private theorem sigPost_concrete_sub_msg {bs : List (BitVec 8)} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostEnv bs evs) :
    SigTryFromPostEnv bs evs := by
  refine seqEnv_mono_local (fun evs₁ hpre => ?_) (fun _ hf => hf) h
  unfold LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget.TryFromPostOutPreEnv at hpre
  unfold SigTryFromPostOutPreEnv
  cases htr : SignalMessage.tryFrom protoSignalCodec bs with
  | error _ =>
    rw [htr] at hpre
    exact hpre
  | ok msg =>
    rw [htr] at hpre
    exact seqEnv_mono_local (fun _ hf => hf)
      (fun _ hok => seqEnv_mono_local (fun _ hct => intoBoxed_concrete_sub_msg hct)
        (fun _ hrest => seqEnv_mono_local (fun _ had => intoBoxedOpt_concrete_sub_msg had)
          (fun _ hcl => hcl) hrest) hok) hpre

private theorem sigMsgCallEnv_sub_bounded (msg : List (BitVec 8)) {evs : List AllocEvent}
    (h : SigMsgCallEnv msg evs) :
    SigTryFromBoundedEnv ⟨0#64, msg, 0#64⟩ evs := by
  cases h with
  | nil =>
    exact Or.inl rfl
  | loopOnly h1 =>
    exact Or.inr (Or.inl (sigLoop_concrete_sub_msg h1))
  | loopPost h1 h2 =>
    exact Or.inr (Or.inr ⟨_, _, rfl, sigLoop_concrete_sub_msg h1, sigPost_concrete_sub_msg h2⟩)

private def PksmTryFromWideEnv (x : PksmGhost) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  SeqEnv (PksmTryFromLoopBoundedEnv x.bytes.length ProtoCaps4.zero)
    (SeqEnv FreeOnlyEvs
      (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x))) evs

private theorem pksmFrom864_sub_afterKyber (xBytes msg : List (BitVec 8)) {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom864PreEnv xBytes msg) FreeOnlyEvs evs) :
    PksmAfterKyberOkEnv xBytes ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom864PreEnv at h
  cases htr : SignalMessage.tryFrom protoSignalCodec msg with
  | error _ =>
    rw [htr] at h
    exact Or.inr (seqEnv_mono_local (fun _ hs => sigMsgCallEnv_sub_bounded msg hs)
      (fun _ hf => Or.inl (Or.inl hf)) h)
  | ok _ =>
    rw [htr] at h
    exact Or.inr
      (seqEnv_mono_local (fun _ hs => sigMsgCallEnv_sub_bounded msg hs) (fun _ hq => hq)
        (seqEnv_push_free_right (fun _ hf => Or.inl (Or.inl hf))
          (fun _ hc => Or.inl (Or.inr hc)) h))

private theorem pksmFrom830_sub_afterKyber (xBytes ik msg : List (BitVec 8))
    {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom830PreEnv xBytes ik msg) FreeOnlyEvs evs) :
    PksmAfterKyberOkEnv xBytes ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom830PreEnv at h
  cases hik : PublicKey.deserialize ik with
  | error _ =>
    rw [hik] at h
    exact Or.inl (seqEnv_nil_freeOnly_sub h)
  | ok _ =>
    rw [hik] at h
    exact pksmFrom864_sub_afterKyber xBytes msg h

private theorem pksmFrom5b4_sub_postBounded (vb : BitVec 8) (xBytes bk ik msg : List (BitVec 8))
    (kpkOpt : Option (BitVec 32)) (kyberOpt : Option (List (BitVec 8)))
    {evs : List AllocEvent}
    (h : SeqEnv (PksmFrom5b4PreEnv vb xBytes bk ik msg kpkOpt kyberOpt) FreeOnlyEvs evs) :
    PksmPostBoundedEnv xBytes kyberOpt ⟨0#64, msg, 0#64⟩ evs := by
  unfold PksmFrom5b4PreEnv at h
  cases hbk : PublicKey.deserialize bk with
  | error _ =>
    rw [hbk] at h
    exact Or.inl (seqEnv_nil_freeOnly_sub h)
  | ok _ =>
    rw [hbk] at h
    unfold PksmFrom684PreEnv at h
    by_cases h1 : (kpkOpt.isSome != kyberOpt.isSome) = true
    · simp only [h1, ↓reduceIte] at h
      exact Or.inr (Or.inl (seqEnv_mono_local (fun _ he => Or.inl he) (fun _ hf => hf) h))
    · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      by_cases h2 : kpkOpt = none ∧ kyberOpt = none ∧ 0x40 ≤ vb.toNat
      · simp only [h2, and_self, ↓reduceIte] at h
        exact Or.inr (Or.inl (seqEnv_mono_local (fun _ he => Or.inr he) (fun _ hf => hf) h))
      · simp only [h2, ↓reduceIte] at h
        have hbox :=
          seqEnv_mono_local (fun _ hb => intoBoxedOpt_concrete_sub_msg hb) (fun _ hq => hq)
            (seqEnv_push_free_right (fun _ hf => Or.inl hf)
              (fun _ hp => pksmFrom830_sub_afterKyber xBytes ik msg hp) h)
        exact Or.inr (Or.inr (Or.inr ⟨[], evs, rfl, freeOnlyEvs_nil_local, hbox⟩))

private theorem pksmAfterLoop_sub_free_post (x : PksmGhost) (vb b1 : BitVec 8)
    (bs1 : List (BitVec 8)) (hx : x.bytes = vb :: b1 :: bs1) {evs₂ : List AllocEvent}
    (h : PksmAfterLoopEnv vb x.bytes (decodeProto (b1 :: bs1)) evs₂) :
    SeqEnv FreeOnlyEvs
      (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)) evs₂ := by
  cases hd : decodeProto (b1 :: bs1) with
  | none =>
    rw [hd] at h
    exact Or.inl h
  | some m =>
    rw [hd] at h
    unfold PksmAfterLoopEnv PksmPostEnv PksmPostPreEnv at h
    rcases hbk : m.baseKey with _ | bk <;>
      rcases hik : m.identityKey with _ | ik <;>
      rcases hmsg : m.message with _ | msg <;>
      rcases hsid : m.signedPreKeyId with _ | sid
    all_goals simp only [hbk, hik, hmsg, hsid] at h
    case some.some.some.some =>
      have hky : pksmDecodedKyberOpt x.bytes = m.kyberCiphertext := by
        rw [hx]; simp [pksmDecodedKyberOpt, hd]
      have hin : pksmInnerGhost x = ⟨0#64, msg, 0#64⟩ := by
        unfold pksmInnerGhost
        rw [hx]
        simp [pksmDecodedInnerBytes, hd, hmsg]
      rw [hky, hin]
      exact seqEnv_free_left_right
        (fun _ hs => pksmFrom5b4_sub_postBounded vb x.bytes bk ik msg m.kyberPreKeyId m.kyberCiphertext hs) h
    all_goals exact Or.inl (seqEnv_nil_freeOnly_sub h)

private theorem pksmTryFromEnv_sub_wide (x : PksmGhost) {evs : List AllocEvent}
    (h : PksmTryFromEnv x evs) : PksmTryFromWideEnv x evs := by
  cases h with
  | nil =>
    exact Or.inl rfl
  | loopOnly hx _ _ hloop =>
    exact Or.inr (Or.inl (sigLoop_concrete_sub_pksmLoop hloop))
  | loopAfter hx _ _ hloop hafter =>
    exact Or.inr (Or.inr ⟨_, _, rfl, sigLoop_concrete_sub_pksmLoop hloop,
      pksmAfterLoop_sub_free_post x _ _ _ hx hafter⟩)

private theorem pksmTryFromWide_phaseCredit (x : PksmGhost) :
    PhaseCreditSpec fineCostModel (PksmTryFromWideEnv x)
      (pksmTryFromDeltaCum x) (pksmTryFromDeltaLive x)
      (pksmTryFromDeltaPeak x) (pksmTryFromMaxReq x) := by
  have hLoop :=
    phaseCreditSpec_protoLoop4_S fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      fineCostModel_wireLowInterceptHyps.hSmallMaxEq (by decide) x.bytes.length
      (phaseCreditSpec_pksmLoopTail_S fineCostModel_modelHyps
        fineCostModel_wireLowInterceptHyps.hSmallMaxEq (by decide))
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hPost0 :=
    phaseCreditSpec_pksmPost_blackbox fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps
      x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)
      (pksmDecodedKyberOpt_length_le x.bytes)
  have hPost :
      PhaseCreditSpec fineCostModel
        (SeqEnv FreeOnlyEvs
          (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)))
        (4 * min x.bytes.length 135167 + 19078 + sigTryFromDeltaCum (pksmInnerGhost x))
        (2 * x.bytes.length + 16390 + sigTryFromDeltaLive (pksmInnerGhost x))
        (2 * x.bytes.length + 16390 + sigTryFromDeltaLive (pksmInnerGhost x) +
          sigTryFromDeltaPeak (pksmInnerGhost x))
        (max 68 (max x.bytes.length (sigTryFromMaxReq (pksmInnerGhost x)))) :=
    (hFree.seq hPost0).mono (by omega) (by omega) (by omega) (by omega)
  have hNil := PhaseCreditSpec.nil fineCostModel
  unfold pksmTryFromDeltaCum pksmTryFromDeltaLive pksmTryFromDeltaPeak pksmTryFromMaxReq
  exact ((hNil.or (hLoop.seq hPost)).of_imp (fun _ he => he)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem pksmTryFromWide_phaseGroup (x : PksmGhost) :
    PhaseGroupSpec fineCostModel (PksmTryFromWideEnv x) (pksmTryFromDeltaGrpS x) := by
  have hLoop := pksmTryFromLoop_phaseGroup fineCostModel_wireGroupHyps x.bytes.length
  unfold pksmTryFromLoopDeltaGrpS at hLoop
  have hFree : PhaseGroupSpec fineCostModel FreeOnlyEvs 0 :=
    PhaseGroupSpec.freeOnly fineCostModel
  have hPost :
      PhaseGroupSpec fineCostModel
        (SeqEnv FreeOnlyEvs
          (PksmPostBoundedEnv x.bytes (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x)))
        (280022 + sigTryFromDeltaGrpS (pksmInnerGhost x)) :=
    (hFree.seq
      (phaseGroupSpec_pksmPost_blackbox fineCostModel_wireGroupHyps x.bytes
        (pksmDecodedKyberOpt x.bytes) (pksmInnerGhost x))).mono (by omega)
  have hNil := PhaseGroupSpec.nil fineCostModel
  unfold pksmTryFromDeltaGrpS
  exact ((hNil.or (hLoop.seq hPost)).of_imp (fun _ he => he)).mono (by omega)

end PksmWireSlicePriv

/-- `fineCostModel` `PhaseCreditSpec` for `PksmTryFromWireSliceEnv` matching `PksmTryFromSliceEnv`. -/
theorem pksmTryFromWireSlice_phaseCredit {rest : List (BitVec 8)}
    (hlen : rest.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel (PksmTryFromWireSliceEnv rest)
      (pksmSliceCum msgCapBytes) (pksmSliceLive msgCapBytes)
      (pksmSlicePeak msgCapBytes) (pksmSliceMaxReq msgCapBytes) := by
  have hWide :=
    (pksmTryFromWide_phaseCredit ⟨0#64, rest, 0#64⟩).of_imp
      (fun _ he => pksmTryFromEnv_sub_wide ⟨0#64, rest, 0#64⟩ he)
  exact hWide.mono
    (LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaCum_le_cap hlen)
    (LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaLive_le_cap hlen)
    (LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaPeak_le_cap hlen)
    (LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromMaxReq_le_cap hlen)

/-- `fineCostModel` `PhaseGroupSpec` for `PksmTryFromWireSliceEnv` matching `PksmTryFromSliceEnv`. -/
theorem pksmTryFromWireSlice_fine_groupSpec {rest : List (BitVec 8)}
    (hlen : rest.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel (PksmTryFromWireSliceEnv rest)
      (pksmTryFromCapDeltaGrpS msgCapBytes) := by
  have hWide :=
    (pksmTryFromWide_phaseGroup ⟨0#64, rest, 0#64⟩).of_imp
      (fun _ he => pksmTryFromEnv_sub_wide ⟨0#64, rest, 0#64⟩ he)
  exact hWide.mono
    (LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit.pksmTryFromDeltaGrpS_le_cap hlen)

/-! ## 2. D3 `pqD3ScopedRun` Callee Envelopes and Whole-`main` `FitsEnv` -/

/-- Binary-kit `CliRunCalleeEnvs` bundle using `PksmTryFromWireSliceEnv` on `pksmEnv` and parametric
`decPkEnv`. -/
def mkD3BinaryKitCalleeEnvsWithDecPk [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop) (g : RunCall) : CliRunCalleeEnvs :=
  { mkBinaryKitRealCalleeEnvsFixed img S X W g with
    pksmEnv := PksmTryFromWireSliceEnv
    decPkEnv := decPkEnv g }

section PqD3RecvPriv

open Arm64 (FsPath FsState normalizePath splitSlash)
open Arm64.Process (ProcessInputs initFsState)
open CryptoVerification.E2E (LocalIdentity djbKey keyPairOf partyAddressName)
open CryptoVerification.LibsignalProtoCodec (WireType encodeBytesField encodeKey)
open CryptoVerification.LibsignalTripleRatchet.Prost (encodeVarint_length_bounds)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure encodeProto3BytesField)
open CryptoVerification.SignalSession
  (Cmd PqParty PqxdhPartyInSpecDomain PublicBundle baseKeysFile bundleDir encodeDir identityFile
   lastResortKyberPreKeyFile oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress pqInitInputs
   pqInputs pqRecvInputs pqSendInputs publicBundleOf sessionFile signedPreKeyFile)
open CryptoVerification.SignalSession.Cli (StoresGhost cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (cliRd pathStr readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_recv)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliDecoupledRamNeed cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
   cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (m5PhaseEnv_groupSpec m6Env_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams W3BinaryInitDom
   W3InitBinaryKitSlotEnv W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams mkBinaryKitRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (R3bEnv initArmDeltaCum initArmMaxReq pksmSliceLive_le_peak r2MaxReq r2TightDeltaCum
   sigSliceCum sigSliceMaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (phaseCredit_or_freeOnly_left)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (OptStageEnv R0BinaryEnv R3aBinaryEnv RunArmBinaryEnv
   cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
   cliRunBinary1MiBCustomPksmCum cliRunBinary1MiBCustomPksmMaxReq
   initArmBinaryPrefixCum m5Phase_Bounded_phaseCredit_fine preEnv_sub_r0BinaryEnv
   r3aRecvWEnv_sub_r3aBinaryEnv r3bRecvPEnv_sub_r3bEnv
   runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget (r3aDecSigGhost0)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRealPksmLiveCap cliRealPksmPeakCap cliRealPksmReqCap
   cliRun1MiBCustomPksmCum cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmMaxReq
   cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS w3InitRealCum w3InitRealGrpS
   w3InitRealLive w3InitRealMaxReq w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec (pathDeltaCum pathMaxReq)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (stdin_le_msgCapBytes_of_pqInputs_and_inputOf stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed cliDecryptSignalSlotEnv_fixed_eq_plain
   dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_own_address
   runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots w3InitBinaryKitSlotEnvFixed_eq_plain)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
  (w2_cliDecryptSignalSlotEnv_sub_binaryKit w3_realCliInitBinarySlotEnv_sub_binaryKit)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (argv_length_le_3_of_pqOrD3Recv cliPqxdhInputs_pqRecvInputs_nil
   cliRunBinaryEnv_fine_groupSpec_of_cap
   cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv d3RecvW4Ext_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (ValidPostSetupWitness cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (fineReadFileMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanMaxReq w1SendRealDcanPeak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanMaxReq
   w2RecvWhisperRealDcanPeak)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bPksmGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)

private theorem exists_cliPqxdhInputs_same_argv_runFiles {P : PEParams} {g : RunCall}
    (hi : CliPqOrD3RecvInputs P g.i) :
    ∃ g₀ : RunCall, CliPqxdhInputs P g₀.i ∧ g₀.c = g.c ∧
      g₀.i.argv = g.i.argv ∧ runFiles g₀.i = runFiles g.i := by
  rcases hi with hi_pq | ⟨st, ct, rc, hwf, hgi⟩
  · exact ⟨g, hi_pq, rfl, rfl, rfl⟩
  · exact ⟨{ g with i := pqRecvInputs P st [] rc },
      cliPqxdhInputs_pqRecvInputs_nil hwf rc, rfl,
      by rw [hgi]; rfl,
      by rw [hgi]; rfl⟩

private def d3KitW3Cum : Nat := w3InitRealCum + 4500000
private def d3KitW3Live : Nat := w3InitRealLive + 65536
private def d3KitW3Peak : Nat := w3InitRealPeak + 65536
private def d3KitW3MaxReq : Nat := w3InitRealMaxReq + 65536
private def d3KitW3GrpS : Nat := w3InitRealGrpS + 1500 * FineScale

private theorem d3KitW3_lp : d3KitW3Live ≤ d3KitW3Peak :=
  Nat.add_le_add_right w3InitReal_caps_le.2.2.1 65536

private def EntriesFromNormP2 (files : List (String × List (BitVec 8))) (fs : FsState) : Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, normalizePath p = k ∧ (p, bs) ∈ files

private theorem entriesFromNormP2_empty (files : List (String × List (BitVec 8))) :
    EntriesFromNormP2 files ({} : FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem entriesFromNormP2_setEntry_dir {files : List (String × List (BitVec 8))}
    {fs : FsState} (h : EntriesFromNormP2 files fs) (pref : FsPath) :
    EntriesFromNormP2 files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold FsState.setEntry at hk; dsimp only at hk; split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromNormP2_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List FsPath) {fs : FsState} (h : EntriesFromNormP2 files fs) :
    EntriesFromNormP2 files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNormP2_setEntry_dir h hd)

private theorem entriesFromNormP2_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : FsState} (h : EntriesFromNormP2 files fs) :
    EntriesFromNormP2 files
      (dirs.foldl
        (fun acc d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (entriesFromNormP2_foldl_dirs _ h)

private theorem entriesFromNormP2_setFile {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFromNormP2 files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFromNormP2 files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold FsState.setFile FsState.setEntry at hk; dsimp only at hk; split at hk
  · rename_i hbeq; injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, (eq_of_beq hbeq).symm, hmem⟩
  · exact h k bs' hk

private theorem entriesFromNormP2_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : FsState} (h : EntriesFromNormP2 allFiles fs) :
    EntriesFromNormP2 allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFromNormP2_foldl_dirs ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast) h
    have hset := entriesFromNormP2_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem initFsState_files_mem_normP2 {inputs : ProcessInputs} {q : String}
    {bs : List (BitVec 8)} (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, normalizePath p = normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := entriesFromNormP2_foldl_outer_dirs inputs.dirs (entriesFromNormP2_empty inputs.files)
  have hf := entriesFromNormP2_foldl_files inputs.files (fun _ hx => hx) hd
  unfold FsState.files FsState.getEntry at h
  split at h
  · cases h
  · exact hf (normalizePath q) bs h

private theorem splitSlash_go_append_slashP2 (cur a b : List Char) :
    splitSlash.go cur (a ++ ('/' :: b)) = splitSlash.go cur a ++ splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, splitSlash.go, ih []]
    · rw [List.cons_append, splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem norm_dir_slash_ne_ikp {s tail dir : String}
    (hs : s.toList = dir.toList ++ ['/'])
    (hd : normalizePath dir = [dir])
    (hne : dir ≠ "identity-key-pair") :
    normalizePath (s ++ tail) ≠ ["identity-key-pair"] := by
  have hsp : splitSlash (s ++ tail) = splitSlash dir ++ splitSlash tail := by
    unfold splitSlash
    rw [String.toList_append, hs, List.append_assoc, List.singleton_append]
    exact splitSlash_go_append_slashP2 [] dir.toList tail.toList
  have hn : normalizePath (s ++ tail) = normalizePath dir ++ normalizePath tail := by
    unfold normalizePath
    rw [hsp, List.filter_append]
  rw [hn, hd, List.singleton_append]
  intro h; injection h with h1 _; exact hne h1

private def kutf8P2 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_dataP2 : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem pathStr_utf8_eqP2 {s : String} (h : pathStr (kutf8P2 s) = s) :
    pathStr (utf8 s) = s := by
  have hu : utf8 s = kutf8P2 s := by
    obtain ⟨l, rfl⟩ := s.exists_eq_ofList
    simp [utf8, kutf8P2, List.utf8Encode, byteArray_toList_eq_dataP2]
  rw [hu]; exact h

private theorem encodeKey_length_le_10P2 (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 := by
  unfold encodeKey; exact (encodeVarint_length_bounds _).2

private theorem encodeProto3BytesField_length_leP2 (tag : Nat) (v : List (BitVec 8)) :
    (encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold encodeProto3BytesField encodeBytesField
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10P2 tag .lengthDelimited
    have hv := (encodeVarint_length_bounds (BitVec.ofNat 64 v.length)).2
    omega

private theorem identityKeyPair_encode_length_le_105P2 (W : PEParams) (me : LocalIdentity) :
    (IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C me.idPriv).publicKey.bytes, me.idPriv.toList⟩).length ≤ 105 := by
  unfold IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3BytesField_length_leP2 1 (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes)
  have h2 := encodeProto3BytesField_length_leP2 2 me.idPriv.toList
  have hdjb : (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
  have hpriv : me.idPriv.toList.length = 32 := me.idPriv.toList_length
  omega

private theorem ownIkp_le_105_of_cliPqInputs {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ bs, StoresGhost.opened.identity.own.get cliIo.rd (runFiles i)
      (utf8 "identity-key-pair") = .ok bs → bs.length ≤ 105 := by
  intro bs hrd
  change cliRd (initFsState (cliInputs i)).files
    (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
  have hnil_or_some : bs = [] ∨
      (initFsState (cliInputs i)).files
        (pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair"))) =
        some (.file bs) := by
    unfold cliRd at hrd
    split at hrd
    · cases hrd
    · rename_i rbs hrv; injection hrd with h; subst h
      unfold readViewF at hrv; split at hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl
      · split at hrv
        · rename_i fbs hfp
          split at hrv
          · injection hrv with h; subst h; exact Or.inr hfp
          · cases hrv
        · cases hrv
        · injection hrv with h; subst h; exact Or.inl rfl
  rcases hnil_or_some with rfl | hfile
  · exact Nat.zero_le 105
  · obtain ⟨p, hp_norm, hmem⟩ := initFsState_files_mem_normP2 hfile
    have hikp_norm : normalizePath
        (pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair"))) =
        ["identity-key-pair"] := by
      change normalizePath (pathStr (utf8 "identity-key-pair")) = ["identity-key-pair"]
      rw [pathStr_utf8_eqP2 rfl]
      decide
    rw [hikp_norm] at hp_norm
    rcases hi with ⟨st, _, hcase⟩
    have hmem' : (p, bs) ∈ i.files := hmem
    have hin_ed : (p, bs) ∈ encodeDir P st := by
      rcases hcase with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
          ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
      · change (p, bs) ∈ (encodeDir P st ++ (publicBundleOf b).files bundleDir) ++
            [(CryptoVerification.SignalSession.coinsFile, t.toList)] at hmem'
        rw [List.mem_append, List.mem_append, List.mem_singleton] at hmem'
        rcases hmem' with (hed | hbun) | hcoins
        · exact hed
        · simp only [PublicBundle.files, bundleDir, List.cons_append,
            List.nil_append, List.mem_cons] at hbun
          rcases hbun with hb1 | hb2 | hb3 | hb4 | hbun
          · injection hb1 with hp_b _; subst hp_b; exact absurd hp_norm (by decide)
          · injection hb2 with hp_b _; subst hp_b; exact absurd hp_norm (by decide)
          · injection hb3 with hp_b _; subst hp_b; exact absurd hp_norm (by decide)
          · injection hb4 with hp_b _; subst hp_b; exact absurd hp_norm (by decide)
          · cases ho : (publicBundleOf b).oneTime with
            | none => rw [ho] at hbun; cases hbun
            | some _ =>
              rw [ho] at hbun
              have hb5 := List.mem_singleton.mp hbun
              injection hb5 with hp_b _; subst hp_b
              exact absurd hp_norm (by decide)
        · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
      · change (p, bs) ∈ (encodeDir P st ++ []) ++
            [(CryptoVerification.SignalSession.coinsFile, r.toList)] at hmem'
        rw [List.append_nil, List.mem_append, List.mem_singleton] at hmem'
        rcases hmem' with hed | hcoins
        · exact hed
        · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
      · change (p, bs) ∈ (encodeDir P st ++ []) ++
            [(CryptoVerification.SignalSession.coinsFile, CryptoGames.HMAC.keyToBytes32 rc)] at hmem'
        rw [List.append_nil, List.mem_append, List.mem_singleton] at hmem'
        rcases hmem' with hed | hcoins
        · exact hed
        · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
      · change (p, bs) ∈ (encodeDir P st ++ []) ++
            [(CryptoVerification.SignalSession.coinsFile, CryptoGames.HMAC.keyToBytes32 rc)] at hmem'
        rw [List.append_nil, List.mem_append, List.mem_singleton] at hmem'
        rcases hmem' with hed | hcoins
        · exact hed
        · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
      · change (p, bs) ∈ (encodeDir P st ++ []) ++
            [(CryptoVerification.SignalSession.coinsFile, CryptoGames.HMAC.keyToBytes32 rc)] at hmem'
        rw [List.append_nil, List.mem_append, List.mem_singleton] at hmem'
        rcases hmem' with hed | hcoins
        · exact hed
        · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    unfold encodeDir at hin_ed
    simp only [List.mem_append] at hin_ed
    rcases hin_ed with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
      rcases hf_hdr with h_ad | h_ikp | h_reg
      · injection h_ad with hp_a _; subst hp_a; exact absurd hp_norm (by decide)
      · injection h_ikp with _ hbs; subst hbs
        exact identityKeyPair_encode_length_le_105P2 P st.me
      · injection h_reg with hp_r _; subst hp_r; exact absurd hp_norm (by decide)
    · cases hp_opt : st.peerId with
      | none => simp [hp_opt] at hf_peer
      | some _ =>
        simp only [hp_opt, List.mem_singleton] at hf_peer
        injection hf_peer with hp_p _; subst hp_p
        exact absurd hp_norm
          (norm_dir_slash_ne_ikp (dir := "identities") (by decide) (by decide) (by decide))
    · cases hs_opt : st.session with
      | none => simp [hs_opt] at hf_sess
      | some _ =>
        simp only [hs_opt, List.mem_singleton] at hf_sess
        injection hf_sess with hp_s _; subst hp_s
        exact absurd hp_norm
          (norm_dir_slash_ne_ikp (dir := "sessions") (by decide) (by decide) (by decide))
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨id, _⟩, _, h_eq⟩
      injection h_eq with hp_s _; subst hp_s
      exact absurd hp_norm
        (norm_dir_slash_ne_ikp (dir := "signed-pre-keys") (by decide) (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨id, _⟩, _, h_eq⟩
      injection h_eq with hp_s _; subst hp_s
      exact absurd hp_norm
        (norm_dir_slash_ne_ikp (dir := "one-time-pre-keys") (by decide) (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨id, _⟩, _, h_eq⟩
      injection h_eq with hp_s _; subst hp_s
      exact absurd hp_norm
        (norm_dir_slash_ne_ikp (dir := "one-time-kyber-pre-keys") (by decide) (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨sub, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨id, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h_eq | h_eq
      · injection h_eq with hp_s _; subst hp_s
        exact absurd hp_norm
          (norm_dir_slash_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide) (by decide))
      · injection h_eq with hp_s _; subst hp_s
        unfold baseKeysFile at hp_norm
        rw [String.append_assoc] at hp_norm
        exact absurd hp_norm
          (norm_dir_slash_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide) (by decide))

private theorem initEnv_eq_w3Fixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i) :
    (mkBinaryKitRealCalleeEnvs img S X W g).initEnv =
      (match g.c with
       | .init _ _ => fun evs =>
         ∃ w : CliRealBinaryKitEnvs.W3BinaryInitParams,
           W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
       | _ => fun _ => False) := by
  obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  funext evs
  dsimp only [mkBinaryKitRealCalleeEnvs]
  cases hc : g.c with
  | init peerAddr dir =>
    dsimp only
    exact propext ⟨fun ⟨w, hdom, hslot⟩ =>
      ⟨w, hdom, Eq.mpr
        (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi₀
          ((hdom peerAddr dir rfl).2.2.1.trans hfiles₀.symm)) evs) hslot⟩,
      fun ⟨w, hdom, hslotF⟩ =>
      ⟨w, hdom, Eq.mp
        (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi₀
          ((hdom peerAddr dir rfl).2.2.1.trans hfiles₀.symm)) evs) hslotF⟩⟩
  | keygen _ _ => rfl
  | send _ => rfl
  | recv _ => rfl

private theorem d3KitW3_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseCreditSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).initEnv
      d3KitW3Cum d3KitW3Live d3KitW3Peak d3KitW3MaxReq := by
  obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  rw [initEnv_eq_w3Fixed img S X W hi]
  exact (binaryKitW3Fixed_fineSpec g (fun bs hrd =>
    ownIkp_le_105_of_cliPqInputs hi₀ bs (hfiles₀.symm ▸ hrd))).credit

private theorem d3KitW3_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseGroupSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).initEnv d3KitW3GrpS := by
  obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  rw [initEnv_eq_w3Fixed img S X W hi]
  exact (binaryKitW3Fixed_fineSpec g (fun bs hrd =>
    ownIkp_le_105_of_cliPqInputs hi₀ bs (hfiles₀.symm ▸ hrd))).groups

private theorem w1Dom_congr_runFiles {c : CallV} {i i₀ : Inputs} {w : W1BinarySendParams}
    (hf : runFiles i₀ = runFiles i) :
    W1BinarySendDom c i w ↔ W1BinarySendDom c i₀ w :=
  ⟨fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3, h4, h5.trans hf.symm⟩,
   fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3, h4, h5.trans hf⟩⟩

private theorem w2Dom_congr_runFiles {c : CallV} {i i₀ : Inputs} {w : W2BinaryWhisperParams}
    (hf : runFiles i₀ = runFiles i) :
    W2BinaryWhisperDom c i w ↔ W2BinaryWhisperDom c i₀ w :=
  ⟨fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3, h4, h5.trans hf.symm⟩,
   fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3, h4, h5.trans hf⟩⟩

private theorem w4Dom_congr_runFiles {c : CallV} {i i₀ : Inputs} {w : W4BinaryRecvPrekeyParams}
    (hf : runFiles i₀ = runFiles i) :
    W4BinaryRecvPrekeyDom c i w ↔ W4BinaryRecvPrekeyDom c i₀ w :=
  ⟨fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3.trans hf.symm, h4, h5⟩,
   fun hd p hp => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hd p hp
    exact ⟨h1, h2, h3.trans hf, h4, h5⟩⟩

private theorem encEnv_congr_runFiles [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g g₀ : RunCall} (hc : g₀.c = g.c) (hf : runFiles g₀.i = runFiles g.i) :
    (mkBinaryKitRealCalleeEnvs img S X W g).encEnv =
      (mkBinaryKitRealCalleeEnvs img S X W g₀).encEnv := by
  funext evs
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [← hc]
  cases g₀.c with
  | send _ =>
    dsimp only
    exact propext ⟨fun ⟨w, hd, hs⟩ => ⟨w, (w1Dom_congr_runFiles hf).mp hd, hs⟩,
      fun ⟨w, hd, hs⟩ => ⟨w, (w1Dom_congr_runFiles hf).mpr hd, hs⟩⟩
  | keygen _ _ => rfl
  | init _ _ => rfl
  | recv _ => rfl

private theorem decSigEnv_congr_runFiles [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g g₀ : RunCall} (hc : g₀.c = g.c) (hf : runFiles g₀.i = runFiles g.i) :
    (mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv =
      (mkBinaryKitRealCalleeEnvs img S X W g₀).decSigEnv := by
  funext evs
  dsimp only [mkBinaryKitRealCalleeEnvs]
  rw [← hc]
  cases g₀.c with
  | recv _ =>
    dsimp only
    exact propext ⟨fun ⟨w, hd, hs⟩ => ⟨w, (w2Dom_congr_runFiles hf).mp hd, hs⟩,
      fun ⟨w, hd, hs⟩ => ⟨w, (w2Dom_congr_runFiles hf).mpr hd, hs⟩⟩
  | keygen _ _ => rfl
  | init _ _ => rfl
  | send _ => rfl

private theorem decPkEnvFixed_congr_runFiles [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g g₀ : RunCall} (hc : g₀.c = g.c) (hf : runFiles g₀.i = runFiles g.i) :
    (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv =
      (mkBinaryKitRealCalleeEnvsFixed img S X W g₀).decPkEnv := by
  funext evs
  dsimp only [mkBinaryKitRealCalleeEnvsFixed]
  rw [← hc]
  cases g₀.c with
  | recv _ =>
    dsimp only
    exact propext ⟨fun ⟨w, hd, hs⟩ => ⟨w, (w4Dom_congr_runFiles hf).mp hd, hs⟩,
      fun ⟨w, hd, hs⟩ => ⟨w, (w4Dom_congr_runFiles hf).mpr hd, hs⟩⟩
  | keygen _ _ => rfl
  | init _ _ => rfl
  | send _ => rfl

private theorem d3KitW1_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).encEnv
      w1SendRealDcanCum w1SendRealDcanPeak w1SendRealDcanPeak w1SendRealDcanMaxReq := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [encEnv_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW1_fineSpec img S X W g₀ hi₀ hparse₀).credit

private theorem d3KitW1_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).encEnv
      w1SendRealDcanGrpS := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [encEnv_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW1_fineSpec img S X W g₀ hi₀ hparse₀).groups

private theorem d3KitW2_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv
      w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcanPeak
      w2RecvWhisperRealDcanMaxReq := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [decSigEnv_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW2_fineSpec img S X W g₀ hi₀ hparse₀).credit

private theorem d3KitW2_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel (mkBinaryKitRealCalleeEnvs img S X W g).decSigEnv
      w2RecvWhisperRealDcanGrpS := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [decSigEnv_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW2_fineSpec img S X W g₀ hi₀ hparse₀).groups

private theorem d3KitW4Fixed_credit [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseCreditSpec fineCostModel (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv
      binaryKitW4FixedCum binaryKitW4FixedLive binaryKitW4FixedPeak binaryKitW4FixedMaxReq := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [decPkEnvFixed_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW4Fixed_fineSpec img S X W g₀ hi₀ hparse₀).credit

private theorem d3KitW4Fixed_groups [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    PhaseGroupSpec fineCostModel (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv
      binaryKitW4FixedGrpS := by
  obtain ⟨g₀, hi₀, hc₀, harg₀, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some g₀.c := by
    rw [harg₀, hc₀]; exact hparse
  rw [decPkEnvFixed_congr_runFiles img S X W hc₀ hfiles₀]
  exact (binaryKitW4Fixed_fineSpec img S X W g₀ hi₀ hparse₀).groups

private def d3BinaryKitCalleeFineSpecs [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (decPkEnv g))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    CliRealCalleeFineSpecs (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv g) where
  initCum := d3KitW3Cum
  initLive := d3KitW3Live
  initPeak := d3KitW3Peak
  initMaxReq := d3KitW3MaxReq
  initGrpS := d3KitW3GrpS
  init_spec := d3KitW3_credit img S X W hi
  init_lp := d3KitW3_lp
  init_grp := d3KitW3_groups img S X W hi
  encCum := w1SendRealDcanCum
  encLive := w1SendRealDcanPeak
  encPeak := w1SendRealDcanPeak
  encMaxReq := w1SendRealDcanMaxReq
  encGrpS := w1SendRealDcanGrpS
  enc_spec := d3KitW1_credit img S X W hi hparse
  enc_lp := Nat.le_refl _
  enc_grp := d3KitW1_groups img S X W hi hparse
  decSigCum := w2RecvWhisperRealDcanCum
  decSigLive := w2RecvWhisperRealDcanPeak
  decSigPeak := w2RecvWhisperRealDcanPeak
  decSigMaxReq := w2RecvWhisperRealDcanMaxReq
  decSigGrpS := w2RecvWhisperRealDcanGrpS
  decSig_spec := d3KitW2_credit img S X W hi hparse
  decSig_lp := Nat.le_refl _
  decSig_grp := d3KitW2_groups img S X W hi hparse
  pksmCum := pksmSliceCum msgCapBytes
  pksmLive := pksmSliceLive msgCapBytes
  pksmPeak := pksmSlicePeak msgCapBytes
  pksmMaxReq := pksmSliceMaxReq msgCapBytes
  pksmGrpS := pksmTryFromCapDeltaGrpS msgCapBytes
  pksm_spec := fun _ hrest => pksmTryFromWireSlice_phaseCredit hrest
  pksm_lp := pksmSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmTryFromWireSlice_fine_groupSpec hrest
  decPkCum := S_pk.cum
  decPkLive := S_pk.live
  decPkPeak := S_pk.peak
  decPkMaxReq := S_pk.maxReq
  decPkGrpS := S_pk.grpS
  decPk_spec := S_pk.credit
  decPk_lp := S_pk.live_le_peak
  decPk_grp := S_pk.groups

private def d3KitRunCum : Nat :=
  cliRun1MiBCustomPksmCum (pksmSliceCum msgCapBytes) d3KitW3Cum
    w1SendRealDcanCum w2RecvWhisperRealDcanCum binaryKitW4FixedCum

private def d3KitRunLive : Nat :=
  cliRun1MiBCustomPksmLive cliRealPksmLiveCap d3KitW3Live
    w1SendRealDcanPeak w2RecvWhisperRealDcanPeak binaryKitW4FixedLive

private def d3KitRunPeak : Nat :=
  cliRun1MiBCustomPksmPeak cliRealPksmLiveCap cliRealPksmPeakCap
    d3KitW3Peak w1SendRealDcanPeak w1SendRealDcanPeak w2RecvWhisperRealDcanPeak binaryKitW4FixedPeak

private def d3KitRunMaxReq : Nat :=
  cliRun1MiBCustomPksmMaxReq cliRealPksmReqCap d3KitW3MaxReq
    w1SendRealDcanMaxReq w2RecvWhisperRealDcanMaxReq binaryKitW4FixedMaxReq

private def d3KitRunGrpS : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes (pksmTryFromCapDeltaGrpS msgCapBytes) d3KitW3GrpS
    w1SendRealDcanGrpS w2RecvWhisperRealDcanGrpS binaryKitW4FixedGrpS

private def d3KitBinaryRunGrpS : Nat := d3KitRunGrpS + 27 * FineScale

private def d3KitMainCum : Nat :=
  123250 + m3PhaseDeltaCum_tight + d3KitRunCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

private def d3KitMainLive : Nat := cliMainTightLiveOf d3KitRunLive
private def d3KitMainPeak : Nat := cliMainTightPeakOf d3KitRunLive d3KitRunPeak
private def d3KitMainReq : Nat :=
  max (max (16 * 2048) 16384) (cliMainTightReqOf d3KitRunMaxReq)

private def d3KitMainGrpS : Nat :=
  cliMainWidenedSetupFineGrpS + d3KitBinaryRunGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

private theorem max_mono_p2 {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left _ _), Nat.le_trans h2 (Nat.le_max_right _ _)⟩

private theorem max4_le_p2 {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : Nat}
    (h1 : a₁ ≤ b₁) (h2 : a₂ ≤ b₂) (h3 : a₃ ≤ b₃) (h4 : a₄ ≤ b₄) :
    max a₁ (max a₂ (max a₃ a₄)) ≤ max b₁ (max b₂ (max b₃ b₄)) :=
  max_mono_p2 h1 (max_mono_p2 h2 (max_mono_p2 h3 h4))

private theorem d3KitMain_arith_bounds :
    d3KitMainLive ≤ d3KitMainPeak ∧
    cliDecoupledRamNeed cliDefaultStaticBytes d3KitMainCum d3KitMainPeak
      d3KitMainReq ((d3KitMainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount d3KitMainCum
      d3KitMainPeak d3KitMainReq ((d3KitMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by unfold d3KitMainLive d3KitMainPeak cliMainTightLiveOf cliMainTightPeakOf
        cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   by decide,
   by decide⟩

private theorem optStage_phaseCredit_p2 {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem optStage_groupSpec_p2 {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem d3BinaryKitCalleeFineSpecs_bounds [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {decPkEnv : RunCall → List AllocEvent → Prop} {g : RunCall}
    (S_pk : SingleSlotFineSpec (decPkEnv g))
    (hCaps : S_pk.cum ≤ binaryKitW4FixedCum ∧
      S_pk.live ≤ binaryKitW4FixedLive ∧
      S_pk.peak ≤ binaryKitW4FixedPeak ∧
      S_pk.maxReq ≤ binaryKitW4FixedMaxReq ∧
      S_pk.grpS ≤ binaryKitW4FixedGrpS)
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    let SE := d3BinaryKitCalleeFineSpecs img S X W S_pk hi hparse
    cliRunBinary1MiBCustomPksmCum SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      d3KitRunCum ∧
    cliRun1MiBCustomPksmLive SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      d3KitRunLive ∧
    cliRun1MiBCustomPksmPeak SE.pksmLive SE.pksmPeak
      SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      d3KitRunPeak ∧
    cliRunBinary1MiBCustomPksmMaxReq SE.pksmMaxReq SE.initMaxReq SE.encMaxReq
      SE.decSigMaxReq SE.decPkMaxReq ≤ d3KitRunMaxReq ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes SE.pksmGrpS
      SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      d3KitRunGrpS := by
  rcases hCaps with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [d3BinaryKitCalleeFineSpecs]
  have hi_cum : max (initArmDeltaCum (pathDeltaCum 26 16) 1637 d3KitW3Cum)
      (initArmBinaryPrefixCum + d3KitW3Cum) ≤
      max (r2TightDeltaCum w1SendRealDcanCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + w2RecvWhisperRealDcanCum)
          (pksmSliceCum msgCapBytes + binaryKitW4FixedCum)) := by decide
  have hi_req : max (initArmMaxReq (pathMaxReq 26 16) 1637 d3KitW3MaxReq)
      (max (fineReadFileMaxReq 1637) d3KitW3MaxReq) ≤
      max (r2MaxReq w1SendRealDcanMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) w2RecvWhisperRealDcanMaxReq)
          (max cliRealPksmReqCap binaryKitW4FixedMaxReq)) := by decide
  have hpk_live : pksmSliceLive msgCapBytes ≤ cliRealPksmLiveCap := by decide
  have hpk_peak : pksmSlicePeak msgCapBytes ≤ cliRealPksmPeakCap := by decide
  have hpk_req : pksmSliceMaxReq msgCapBytes ≤ cliRealPksmReqCap := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold d3KitRunCum cliRunBinary1MiBCustomPksmCum cliRun1MiBCustomPksmCum
    exact Nat.add_le_add_left (Nat.max_le.mpr
      ⟨Nat.le_trans hi_cum (Nat.le_max_right _ _),
       Nat.le_trans (max_mono_p2 (Nat.le_refl _) (max_mono_p2 (Nat.le_refl _)
         (Nat.add_le_add_left hpc _))) (Nat.le_max_right _ _)⟩) _
  · unfold d3KitRunLive cliRun1MiBCustomPksmLive
    exact Nat.add_le_add_left (max4_le_p2 (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add hpk_live hpl)) _
  · unfold d3KitRunPeak cliRun1MiBCustomPksmPeak
    exact max_mono_p2 (Nat.le_refl _) (Nat.add_le_add_left (max4_le_p2 (Nat.le_refl _)
      (Nat.le_refl _) (Nat.le_refl _) (max_mono_p2 hpk_peak (Nat.add_le_add hpk_live hpp))) _)
  · unfold d3KitRunMaxReq cliRunBinary1MiBCustomPksmMaxReq cliRun1MiBCustomPksmMaxReq
    exact max_mono_p2 (Nat.le_refl _) (Nat.max_le.mpr
      ⟨Nat.le_trans hi_req (Nat.le_max_right _ _),
       Nat.le_trans (max_mono_p2 (Nat.le_refl _) (max_mono_p2 (Nat.le_refl _)
         (max_mono_p2 hpk_req hpr))) (Nat.le_max_right _ _)⟩)
  · unfold d3KitRunGrpS cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add_left (max4_le_p2 (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
      (Nat.add_le_add_left hpg _)) _

private theorem parseArgs_pqRecvInputs_is_recv {P : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {c : CallV}
    (hp : parseArgs uuidTryParse ((pqRecvInputs P st ct rc).argv.map bytesOfString) = some c) :
    ∃ peerV : AddrV, c = .recv peerV := by
  have ha : (pqRecvInputs P st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [ha, parseArgs_recv] at hp
  injection hp with hc
  exact ⟨_, hc.symm⟩

private theorem seqEnv_mono_p2 {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (ha : ∀ e, A₁ e → A₂ e) (hb : ∀ e, B₁ e → B₂ e) {evs : List AllocEvent}
    (h : SeqEnv A₁ B₁ evs) : SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨e₁, e₂, rfl, h1, h2⟩
  · exact Or.inl (ha evs h1)
  · exact Or.inr ⟨e₁, e₂, rfl, ha e₁ h1, hb e₂ h2⟩

private theorem realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits_w4Fixed [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop)
    (S_pk : ∀ (g : RunCall),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (decPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ binaryKitW4FixedCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ binaryKitW4FixedLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ binaryKitW4FixedPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ binaryKitW4FixedMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ binaryKitW4FixedGrpS) :
    ∀ i : Inputs, CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i) := by
  intro i hi
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd
          (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (d3KitRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      d3KitRunLive
      (max d3KitRunPeak
        (d3KitRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max d3KitRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
    let SE := d3BinaryKitCalleeFineSpecs img S X W Spk hi_g w.parse_ok
    obtain ⟨h1_cum, h2, h3, h1_req, _⟩ :=
      d3BinaryKitCalleeFineSpecs_bounds img S X W Spk (hCaps w.g hi_g w.stdin_le w.parse_ok)
        hi_g w.parse_ok
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_pqOrD3Recv SE hi_g w.stdin_le
        w.parse_ok).mono h1_cum h2 h3 h1_req
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono_p2 (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono_p2 (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd
            (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (d3KitRunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      d3KitRunLive
      (max d3KitRunPeak
        (d3KitRunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max d3KitRunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i)
      d3KitMainCum d3KitMainLive d3KitMainPeak d3KitMainReq := by
    refine ((cliMainBoundedSetup_phaseCredit_fine (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (optStage_phaseCredit_p2 hex)).mono ?_ ?_ ?_ ?_
    · unfold d3KitMainCum; simp only [Nat.add_assoc]; exact Nat.le_refl _
    · unfold d3KitMainLive cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
    · unfold d3KitMainPeak cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
    · unfold d3KitMainReq cliMainTightReqOf cliMainMaxReq
      have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd
            (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (d3KitBinaryRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Spk := S_pk w.g hi_g w.stdin_le w.parse_ok
        let SE := d3BinaryKitCalleeFineSpecs img S X W Spk hi_g w.parse_ok
        obtain ⟨_, _, _, _, h5⟩ :=
          d3BinaryKitCalleeFineSpecs_bounds img S X W Spk (hCaps w.g hi_g w.stdin_le w.parse_ok)
            hi_g w.parse_ok
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ d3KitRunGrpS - 15 * FineScale := by
          dsimp only [SE, d3BinaryKitCalleeFineSpecs]; decide
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le
          (by decide : 15 * FineScale ≤ d3KitRunGrpS) hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd
                (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv w.g) sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (d3KitBinaryRunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by unfold d3KitBinaryRunGrpS; generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (RealCliMainBinaryEnvOf (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i)
      d3KitMainGrpS :=
    ((cliMainBoundedSetup_fine_groupSpec (argv_length_le_3_of_pqOrD3Recv hi)).seq
      (optStage_groupSpec_p2 hex_grp)).mono
      (by unfold d3KitMainGrpS; generalize FineScale = fs; omega)
  obtain ⟨hlp, hram, hva⟩ := d3KitMain_arith_bounds
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

/-- Whole-`main` `FitsEnv fineCostModel cliBudgetLimits` (`1 GiB`) on `CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`
for `mkD3BinaryKitCalleeEnvsWithDecPk` with any `decPkEnv` bounded by `d3RecvW4Ext*`. -/
theorem realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits [LibsignalPlacement]
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPkEnv : RunCall → List AllocEvent → Prop)
    (S_pk : ∀ (g : RunCall),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      g.i.stdin.length ≤ msgCapBytes →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec (decPkEnv g))
    (hCaps : ∀ (g : RunCall)
      (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
      (hstdin : g.i.stdin.length ≤ msgCapBytes)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      (S_pk g hi_g hstdin hparse).cum ≤ d3RecvW4ExtCum ∧
      (S_pk g hi_g hstdin hparse).live ≤ d3RecvW4ExtLive ∧
      (S_pk g hi_g hstdin hparse).peak ≤ d3RecvW4ExtPeak ∧
      (S_pk g hi_g hstdin hparse).maxReq ≤ d3RecvW4ExtMaxReq ∧
      (S_pk g hi_g hstdin hparse).grpS ≤ d3RecvW4ExtGrpS) :
    ∀ i : Inputs, CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init
        (RealCliMainBinaryEnvOf (mkD3BinaryKitCalleeEnvsWithDecPk img S X W decPkEnv) i) :=
  realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits_w4Fixed img S X W decPkEnv S_pk
    (fun g hi_g hstdin hparse => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hCaps g hi_g hstdin hparse
      exact
        ⟨Nat.le_trans h1 (by decide : d3RecvW4ExtCum ≤ binaryKitW4FixedCum),
         Nat.le_trans h2 (by decide : d3RecvW4ExtLive ≤ binaryKitW4FixedLive),
         Nat.le_trans h3 (by decide : d3RecvW4ExtPeak ≤ binaryKitW4FixedPeak),
         Nat.le_trans h4 (by decide : d3RecvW4ExtMaxReq ≤ binaryKitW4FixedMaxReq),
         Nat.le_trans h5 (by decide : d3RecvW4ExtGrpS ≤ binaryKitW4FixedGrpS)⟩)

/-- Concrete `MainEntryBudgetFitsCapOf` at `cliBudgetLimits` (`1 GiB`) for `pqD3ScopedRun`
(`CliPqOrD3RecvInputs ⟨W.C, W.Q⟩`, covering `PathB`, `ValidMatch`, `Untyped`, `ParseNone`, and
`ValidOver` `> 1 MiB` `stdin` early-exit) whenever `DecPkSlotEnv` embeds call-contextually into
`(mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv` on `CliPqOrD3RecvInputs` prekey calls. -/
theorem mainEntryBudgetFitsCapOf_pqD3Recv_fixed [LibsignalPlacement]
    {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64)
    (hDecPkSub : ∀ (g : RunCall) (meV peerV : AddrV)
      (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      S.pksmParse rest = some pm →
      ∀ evs : List AllocEvent,
        DecPkSlotEnv (r3bDecPkGhost g meV peerV pm) evs →
        (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv evs)
    (hS_enc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn := by rfl)
    (hS_pksm : ∀ (rest : List (BitVec 8)) (pm : PreKeySignalMessage),
      S.pksmParse rest = some pm → pksmParse rest = some pm) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B
            (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) := by
  have _ := hS_pksm
  let E := mkD3BinaryKitCalleeEnvsWithDecPk img S X W
    (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv)
  have hMain := realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits_w4Fixed img S X W
    (fun g => (mkBinaryKitRealCalleeEnvsFixed img S X W g).decPkEnv)
    (fun g hi_g _hstdin hparse =>
      { cum := binaryKitW4FixedCum
        live := binaryKitW4FixedLive
        peak := binaryKitW4FixedPeak
        maxReq := binaryKitW4FixedMaxReq
        grpS := binaryKitW4FixedGrpS
        credit := d3KitW4Fixed_credit img S X W hi_g hparse
        live_le_peak := d3RecvW4Ext_live_le_peak
        groups := d3KitW4Fixed_groups img S X W hi_g hparse })
    (fun _ _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
  exact mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    hMain
    (fun i c hi hp hin => by
      rcases hi with hi_pq | ⟨st, ct, rc, _, rfl⟩
      · exact stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin
      · exact stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin)
    hNwDom
    (fun g hi hparse hin _hrel evs hrun => by
      cases hcmd : g.c with
      | keygen _ _ | init _ _ | send _ =>
        have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i := by
          rcases hi with hpq | ⟨st, ct, rc, _, hgi⟩
          · exact hpq
          · obtain ⟨_, hc_recv⟩ := parseArgs_pqRecvInputs_is_recv (hgi ▸ hparse)
            rw [hcmd] at hc_recv; cases hc_recv
        have hkit := runEnvFixed_sub_realCliRunBinaryKitEnvOfFixed_of_slots img S X W A B hi_pq hin
          (fun peerV dir d2 _ hc _ hpv hpval _ _ _ ⟨w, hx, hF, hspqr, hgv, halice, hslotF⟩ =>
            w3_realCliInitBinarySlotEnv_sub_binaryKit img S X W g peerV dir d2
              hparse hc hpv hpval
              ⟨w, hx, hF, hspqr, hgv, halice,
                Eq.mp (congrFun (w3InitBinaryKitSlotEnvFixed_eq_plain hi_pq (congrArg (·.F) hx)) _)
                  hslotF⟩)
          (fun _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          hS_enc evs hrun
        unfold RealCliRunEnvMemFixed.realCliRunBinaryKitEnvOfFixed at hkit
        unfold CliRunBinaryEnv at hkit ⊢
        rcases hkit with hf | hr0
        · exact Or.inl hf
        · right
          refine seqEnv_mono_p2 (fun _ h => h)
            (fun _ hseq => seqEnv_mono_p2 (fun _ harm => ?_) (fun _ hj => hj) hseq) hr0
          unfold RunArmBinaryEnv at harm ⊢
          dsimp only [E, mkD3BinaryKitCalleeEnvsWithDecPk]
          simp only [hcmd] at harm ⊢
          exact harm
      | recv peerV₀ =>
        obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := exists_cliPqxdhInputs_same_argv_runFiles hi
        have hpeq : PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
            PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
          funext e
          unfold PreEnv cliRunCalleesEnvs
          dsimp only
          rw [← hfiles₀, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi₀)]
        exact runEnv_to_cliRunBinaryEnv_of_slots (E := E g)
          (fun _ hp =>
            preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
              (Eq.mp (congrFun hpeq _) hp))
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ _ _ hc => by rw [hcmd] at hc; cases hc)
          (fun _ peerV rest _ hc hst hrw =>
            r3aRecvWEnv_sub_r3aBinaryEnv
              (fun _ meG m e _hme htr hd =>
                w2_cliDecryptSignalSlotEnv_sub_binaryKit img S X W A B g meG peerV rest m
                  hin hc hst htr
                  (Eq.mp
                    (congrFun
                      (cliDecryptSignalSlotEnv_fixed_eq_plain hi₀ A B
                        (x := r3aDecSigGhost0 g peerV meG m) hfiles₀.symm)
                      e)
                    hd))
              hrw)
          (fun _ peerV rest _ hc hst hrp =>
            r3bRecvPEnv_sub_r3bEnv
              (fun _ hpk => hpk)
              (fun meV _meG pm e _hme hp hd =>
                hDecPkSub g meV peerV rest pm hi hparse hin hc hst hp e hd)
              hrp)
          evs hrun)

end PqD3RecvPriv

/-! ## 3. D3 `initD3ScopedRun` `MainEntryBudgetFitsCapOf` (`cliBudgetLimits`, `1 GiB`) -/

section InitD3Priv

open Arm64 (FsEntry FsPath FsState normalizePath splitSlash)
open Arm64.Process (ProcessInputs initFsState)
open CryptoGames (Party)
open CryptoVerification.E2E
  (LocalIdentity PreKeyBundleFields djbKey initiateTapeLen keyPairOf partyAddressName)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeBytesField encodeKey encodeUint32Field)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchet.Prost (encodeVarint_length_bounds)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure encodeProto3BytesField)
open CryptoVerification.SignalSession
  (Cmd PqParty PqxdhPartyInSpecDomain PublicBundle ancestors baseKeysFile bundleDir cliProcessInputs
   coinsFile dirsFold encodeDir fileCapBytes filesFold filesOf files_eq_entries fsView
   identityKeyPairFile initFsState_entries le32 partyAddress pqInitInputs pqInputs publicBundleOf
   stdioPaths textBytes)
open CryptoVerification.SignalSession.Cli
  (ReadRule StoresGhost cliInputs decimalText pathOf splitId splitSigned utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.MainHops
  (addrParse blockingAncestorF cliRd pathStr readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose
  (Init1Data Init2Data MeAtDispatch addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs (kemPkLen)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps dirDomainCaps_opened_own parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliDecoupledRamNeed cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
   cliMaxAddrTextBytes cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB
   fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (cliIoReadFileEnv_nonFreeBound m5PhaseEnv_groupSpec m6Env_groupSpec phaseGroupSpec_append_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
  (phaseCreditSpec_cliIoReadFile_anyR_tight phaseCredit_allocBytes1_tight)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024 readFileDeltaCum_tight)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W3BinaryInitDom W3BinaryInitParams)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (InitArmEnv JoinEnv R0OpenedEnv R1cEnv SplitIdEnv SplitSignedEnv
   addressTryParseDeltaCum addressTryParseDeltaLive addressTryParseDeltaPeak addressTryParseMaxReq
   addressTryParse_phaseCredit freeOnlyEvs_append initArmDeltaCum initArmDeltaLive initArmDeltaPeak
   initArmMaxReq runArmEnv_nil splitIdDeltaCum splitId_small_phaseCredit splitSignedDeltaCum
   splitSigned_small_phaseCredit utf8_address_length_le utf8_bundleNames_length_le_16)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (phaseCredit_or_freeOnly_left phaseCredit_seq_freeOnly_left phaseCredit_seq_freeOnly_right)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBMaxReq r0Opened1MiBPeak)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (InitArmBinaryCoreEnv InitArmBinaryEnv OptStageEnv PubBundleReadEnv PubSplitIdEnv
   PubSplitSignedEnv R0BinaryEnv R1bBinaryEnv R1bDeserStageEnv R1bFileStepEnv RunArmBinaryEnv
   cliMainBoundedSetup_fine_groupSpec cliMainBoundedSetup_phaseCredit_fine
   init2Stage4Env_sub_r1bDeserStageEnv m5Phase_Bounded_phaseCredit_fine preEnv_sub_r0BinaryEnv
   pubSplitIdEnv_sub_splitIdEnv pubSplitSignedEnv_sub_splitSignedEnv r1bDeserStageCum
   r1cInit3Env_sub_r1cEnv runArmEnv_sub_runArmBinaryEnv splitIdEnv_append_freeOnly
   splitSignedEnv_append_freeOnly)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (cliRunOpenedCustomPksmGrpS w3InitRealCum w3InitRealGrpS w3InitRealLive w3InitRealMaxReq
   w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf cliRunOfR0_fine_groupSpec
   initArmEnv_fine_groupSpec r0OpenedEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers (cliIoCapEvents cliIoReadCaps)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (NonFreeBound)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed dirGetEnv_fixed_eq_of_not_overCap
   not_overCapFile_runFiles_own_address)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (ValidPostSetupWitness cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit (pksmCanonSliceGrpS)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomSpecF3
  (BundleFilesFlatRaw pqInitInputsFRaw)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (OverCapFile)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.CalleesBudget (addressEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity
  (InputsEquivRaw NonBundleCoinsStdio fileStep_entries filesFold_eq_foldl_fileStep
   mem_dropLast_nonEmptyPrefixes_iff runFiles_eq_of_nonBundleCoins)
open LibsignalBinary.Proofs.SignalSession.Cli.Pub.BundleRead.PlacedBudgetAux
  (BundleReadAfterReadEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
  (PreAfterGetEnv PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aProofPlacedBudget
  (Init1AfterReadEnv Init1Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadOpkSpinePlacedBudget
  (R1bStepOpkErrEnv R1bStepOpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bProofPlacedBudget
  (Init2AfterRegOkEnv Init2Env Init2Stage2Env Init2Stage3Env R1bStepKpkErrEnv R1bStepKpkOkEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
  (R1cInit3Env r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight dirGetEnv_path_readFile_groupSpec
   pathEnv_fine_phaseCredit_tight)

private abbrev seqEnv_mono_init := @SeqCreditKit.SeqEnv.mono

private theorem ite_pos_init {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h

private theorem ite_neg_init {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl

private theorem max_self_le_init (a : Nat) : max a a ≤ a :=
  Nat.max_le.mpr ⟨Nat.le_refl a, Nat.le_refl a⟩

private theorem max_mono_init {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private def kutf8_init (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data_init : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8_init (s : String) : utf8 s = kutf8_init s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8_init, List.utf8Encode, byteArray_toList_eq_data_init]

private theorem repr_utf8_eq_kutf8_init (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = kutf8_init s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, kutf8_init, List.utf8Encode,
    byteArray_toList_eq_data_init]

private theorem parseArgs_init_bundleDir_init {peerText : String} {c : CallV}
    (hparse : parseArgs uuidTryParse
      ([bytesOfString "init", bytesOfString peerText, bytesOfString bundleDir]) = some c) :
    ∃ peerV : AddrV, c = .init peerV (bytesOfString bundleDir) := by
  have hin : bytesOfString "init" = utf8 "init" := by rw [utf8_eq_kutf8_init]; decide
  have hkg : utf8 "init" ≠ utf8 "keygen" := by rw [utf8_eq_kutf8_init, utf8_eq_kutf8_init]; decide
  simp only [parseArgs, hin, hkg, ↓reduceIte, Option.map_eq_some_iff] at hparse
  obtain ⟨peerV, _, rfl⟩ := hparse
  exact ⟨peerV, rfl⟩

/-! ### 3a. `CliInitD3Inputs` Agreement with `pqInitInputs` on `own` Store Paths -/

private def zeroBundleInit : PreKeyBundleFields :=
  ⟨0#32, none, 0#32,
   List.Vector.replicate 32 0#8, List.Vector.replicate 64 0#8,
   0#32, List.Vector.replicate 1568 0#8, List.Vector.replicate 64 0#8,
   List.Vector.replicate 32 0#8⟩

private theorem filesFold_entries_of_head_ne_init (l : List (String × List (BitVec 8))) (fs : FsState)
    {q : FsPath} (h : ∀ x ∈ l, (normalizePath x.1).head? ≠ q.head?) :
    (filesFold l fs).entries q = fs.entries q := by
  rw [filesFold_eq_foldl_fileStep]
  induction l generalizing fs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨p, bs⟩
    rw [List.foldl_cons, ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy)), fileStep_entries]
    have hp := h (p, bs) (List.mem_cons_self ..)
    have hneq : q ≠ normalizePath p := fun heq => hp (heq ▸ rfl)
    have hnanc : q ∉ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast := by
      intro hm
      obtain ⟨hqne, ⟨tl, htl⟩, _⟩ := mem_dropLast_nonEmptyPrefixes_iff.mp hm
      cases q with
      | nil => exact hqne rfl
      | cons c qs => exact hp (by rw [← htl, List.cons_append, List.head?_cons, List.head?_cons])
    simp [hneq, hnanc]

private theorem filesOf_eq_none_of_nil_or_stdio_init (f : List (String × List (BitVec 8))) {p : String}
    (h : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath) :
    filesOf f p = none := by
  unfold filesOf fsView
  by_cases hns : normalizePath p ∈ stdioPaths.map normalizePath
  · rw [ite_pos_init hns]
  · rw [ite_neg_init hns]
    rcases h with hnil | hst <;> [rw [files_eq_entries, hnil]; exact absurd hst hns]
    rfl

private theorem filesOf_eq_match_filesFold_init (f : List (String × List (BitVec 8))) {p : String}
    (hne : normalizePath p ≠ [])
    (hns : normalizePath p ∉ stdioPaths.map normalizePath) :
    filesOf f p = match (filesFold f {}).entries (normalizePath p) with
      | some (.file bs) => some bs | _ => none := by
  unfold filesOf fsView
  rw [ite_neg_init hns, files_eq_entries,
    ite_neg_init (by rw [List.isEmpty_eq_false_iff.mpr hne]; decide),
    initFsState_entries ({ files := f } : ProcessInputs) (normalizePath p) hns]
  rfl

private theorem filesOf_append_of_head_ne_init (f₁ f₂ : List (String × List (BitVec 8))) {p : String}
    (h : ∀ x ∈ f₂, (normalizePath x.1).head? ≠ (normalizePath p).head?) :
    filesOf (f₁ ++ f₂) p = filesOf f₁ p := by
  by_cases hbad : normalizePath p = [] ∨ normalizePath p ∈ stdioPaths.map normalizePath
  · rw [filesOf_eq_none_of_nil_or_stdio_init _ hbad, filesOf_eq_none_of_nil_or_stdio_init _ hbad]
  · push Not at hbad
    rw [filesOf_eq_match_filesFold_init _ hbad.1 hbad.2,
      filesOf_eq_match_filesFold_init _ hbad.1 hbad.2,
      show filesFold (f₁ ++ f₂) {} = filesFold f₂ (filesFold f₁ {}) from List.foldl_append,
      filesFold_entries_of_head_ne_init f₂ _ h]

private theorem filesOf_pqInitInputsF_nonBundleCoins_init {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) {p : String} (hp : NonBundleCoinsStdio (normalizePath p)) :
    filesOf i.files p = filesOf (encodeDir P st) p := by
  rw [heq.2.2.2 p, show (pqInitInputsFRaw P st files t).files =
      encodeDir P st ++ (files ++ [(coinsFile, t.toList)]) by
        simp [pqInitInputsFRaw, pqInputs, List.append_assoc]]
  refine filesOf_append_of_head_ne_init _ _ fun x hx hhead => ?_
  rcases List.mem_append.mp hx with hf | hc
  · obtain ⟨⟨_, hnorm⟩, _⟩ := hb x hf
    rw [hnorm, List.head?_cons] at hhead
    exact hp.2.1 hhead.symm
  · rw [List.mem_singleton] at hc
    subst hc
    dsimp only at hhead
    exact hp.2.2.1 (hhead.symm.trans (by decide : (normalizePath coinsFile).head? = some coinsFile))

private theorem filesOf_pqInitZero_nonBundleCoins_init (P : PEParams) (st : PqParty)
    (t : List.Vector (BitVec 8) initiateTapeLen) {p : String}
    (hp : NonBundleCoinsStdio (normalizePath p)) :
    filesOf (pqInitInputs P st zeroBundleInit t).files p = filesOf (encodeDir P st) p := by
  rw [show (pqInitInputs P st zeroBundleInit t).files =
      encodeDir P st ++ ((publicBundleOf zeroBundleInit).files bundleDir ++ [(coinsFile, t.toList)]) by
        simp [pqInitInputs, pqInputs, List.append_assoc]]
  refine filesOf_append_of_head_ne_init _ _ fun x hx hhead => ?_
  rcases List.mem_append.mp hx with hf | hc
  · simp only [publicBundleOf, PublicBundle.files, zeroBundleInit, Option.map,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact hp.2.1 (hhead.symm.trans (by decide))
    · exact hp.2.1 (hhead.symm.trans (by decide))
    · exact hp.2.1 (hhead.symm.trans (by decide))
    · exact hp.2.1 (hhead.symm.trans (by decide))
  · rw [List.mem_singleton] at hc
    subst hc
    dsimp only at hhead
    exact hp.2.2.1 (hhead.symm.trans (by decide : (normalizePath coinsFile).head? = some coinsFile))

private theorem runFiles_eq_pqInitZero_of_nonBundleCoins {P : PEParams} {st : PqParty}
    {files : List (String × List (BitVec 8))} {t : List.Vector (BitVec 8) initiateTapeLen}
    {i : Inputs} (heq : InputsEquivRaw i (pqInitInputsFRaw P st files t))
    (hb : BundleFilesFlatRaw files) :
    ∀ p : String, NonBundleCoinsStdio (normalizePath p) →
      runFiles i p = runFiles (pqInitInputs P st zeroBundleInit t) p :=
  runFiles_eq_of_nonBundleCoins heq.2.1 (fun _p hp =>
    (filesOf_pqInitInputsF_nonBundleCoins_init heq hb hp).trans
      (filesOf_pqInitZero_nonBundleCoins_init P st t hp).symm)

private theorem pathStr_utf8_address : pathStr (utf8 "address") = "address" := by
  rw [utf8_eq_kutf8_init]; rfl

private theorem pathStr_utf8_ikp : pathStr (utf8 "identity-key-pair") = "identity-key-pair" := by
  rw [utf8_eq_kutf8_init]; rfl

private theorem nonBundleCoins_address : NonBundleCoinsStdio (normalizePath "address") :=
  ⟨by decide, by decide, by decide, by decide⟩

private theorem nonBundleCoins_ikp : NonBundleCoinsStdio (normalizePath "identity-key-pair") :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### 3b. `identity-key-pair` `≤ 105`-Byte Cap & `"address"` Non-Over-Cap on `CliInitD3Inputs` -/

private def EntriesFromNormInit (files : List (String × List (BitVec 8))) (fs : FsState) : Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, normalizePath p = k ∧ (p, bs) ∈ files

private theorem entriesFromNormInit_empty (files : List (String × List (BitVec 8))) :
    EntriesFromNormInit files ({} : FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem entriesFromNormInit_setDir {files : List (String × List (BitVec 8))}
    {fs : FsState} (h : EntriesFromNormInit files fs) (pref : FsPath) :
    EntriesFromNormInit files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem entriesFromNormInit_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List FsPath) {fs : FsState} (h : EntriesFromNormInit files fs) :
    EntriesFromNormInit files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd _ ih => exact ih (entriesFromNormInit_setDir h hd)

private theorem entriesFromNormInit_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : FsState} (h : EntriesFromNormInit files fs) :
    EntriesFromNormInit files
      (dirs.foldl
        (fun acc d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons _ _ ih => exact ih (entriesFromNormInit_foldl_dirs _ h)

private theorem entriesFromNormInit_setFile {files : List (String × List (BitVec 8))} {fs : FsState}
    (h : EntriesFromNormInit files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    EntriesFromNormInit files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk
  unfold FsState.setFile FsState.setEntry at hk
  dsimp only at hk
  split at hk
  · rename_i hbeq
    injection hk with hfile
    injection hfile with hbs
    subst hbs
    exact ⟨p, (eq_of_beq hbeq).symm, hmem⟩
  · exact h k bs' hk

private theorem entriesFromNormInit_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : FsState} (h : EntriesFromNormInit allFiles fs) :
    EntriesFromNormInit allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
            (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := entriesFromNormInit_foldl_dirs ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast) h
    have hset := entriesFromNormInit_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem initFsState_files_mem_norm_init {inputs : ProcessInputs} {q : String}
    {bs : List (BitVec 8)} (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, normalizePath p = normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := entriesFromNormInit_foldl_outer_dirs inputs.dirs (entriesFromNormInit_empty inputs.files)
  have hf := entriesFromNormInit_foldl_files inputs.files (fun _ hx => hx) hd
  unfold FsState.files FsState.getEntry at h
  split at h
  · cases h
  · exact hf (normalizePath q) bs h

private theorem splitSlash_go_append_slash_init (cur a b : List Char) :
    splitSlash.go cur (a ++ ('/' :: b)) = splitSlash.go cur a ++ splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, splitSlash.go, ih []]
    · rw [List.cons_append, splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem normalizePath_append_slash_init (a b : String) :
    normalizePath (a ++ "/" ++ b) = normalizePath a ++ normalizePath b := by
  unfold normalizePath
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold splitSlash
  rw [htl, splitSlash_go_append_slash_init [] a.toList b.toList, List.filter_append]

private theorem encodeKey_length_le_10_init (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 := by
  unfold encodeKey
  exact (encodeVarint_length_bounds _).2

private theorem encodeProto3BytesField_length_le_init (tag : Nat) (v : List (BitVec 8)) :
    (encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold encodeProto3BytesField encodeBytesField
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := encodeKey_length_le_10_init tag .lengthDelimited
    have hv := (encodeVarint_length_bounds (BitVec.ofNat 64 v.length)).2
    omega

private theorem partyAddress_textBytes_length_le_40_init (p : Party) :
    (textBytes (partyAddress p).text).length ≤ 40 := by
  unfold textBytes partyAddress CryptoVerification.SignalSession.Address.text
  dsimp only
  rw [repr_utf8_eq_kutf8_init]
  have hk_app (a b : String) : kutf8_init (a ++ b) = kutf8_init a ++ kutf8_init b := by
    simp [kutf8_init, String.toList_append, List.flatMap_append]
  rw [hk_app, hk_app, List.length_append, List.length_append]
  have hd : (kutf8_init (toString (1 : Nat))).length ≤ 1 := by
    rw [← utf8_eq_kutf8_init]
    exact decimalText_length_le 1 1 (by omega) (by omega)
  have hdot : (kutf8_init ".").length = 1 := rfl
  have hp : (kutf8_init (partyAddressName p)).length = 36 := by cases p <;> rfl
  omega

private theorem identityKeyPair_encode_length_le_105_init (W : PEParams) (me : LocalIdentity) :
    (IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf W.C me.idPriv).publicKey.bytes, me.idPriv.toList⟩).length ≤ 105 := by
  unfold IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := encodeProto3BytesField_length_le_init 1 (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes)
  have h2 := encodeProto3BytesField_length_le_init 2 me.idPriv.toList
  have hdjb : (djbKey (keyPairOf W.C me.idPriv).publicKey.bytes).length = 33 := by simp [djbKey]
  have hpriv : me.idPriv.toList.length = 32 := me.idPriv.toList_length
  omega

private theorem norm_dir_slash_ne_seg {s tail dir seg : String}
    (hs : s.toList = dir.toList ++ ['/'])
    (hd : normalizePath dir = [dir])
    (hne : dir ≠ seg) :
    normalizePath (s ++ tail) ≠ [seg] := by
  have hsp : splitSlash (s ++ tail) = splitSlash dir ++ splitSlash tail := by
    unfold splitSlash
    rw [String.toList_append, hs, List.append_assoc, List.singleton_append]
    exact splitSlash_go_append_slash_init [] dir.toList tail.toList
  have hn : normalizePath (s ++ tail) = normalizePath dir ++ normalizePath tail := by
    unfold normalizePath
    rw [hsp, List.filter_append]
  rw [hn, hd, List.singleton_append]
  intro heq
  injection heq with h1 _
  exact hne h1

private theorem pqInitZero_singleSeg_file_le_105 {P : PEParams} {st : PqParty}
    {t : List.Vector (BitVec 8) initiateTapeLen} (hs : st.session = none)
    {seg : String} {bs : List (BitVec 8)}
    (hnorm_seg : normalizePath seg = [seg])
    (hne_sig : "signed-pre-keys" ≠ seg)
    (hne_ot : "one-time-pre-keys" ≠ seg)
    (hne_kot : "one-time-kyber-pre-keys" ≠ seg)
    (hne_klr : "last-resort-kyber-pre-keys" ≠ seg)
    (hne_b1 : normalizePath (bundleDir ++ "/identity-key") ≠ [seg])
    (hne_b2 : normalizePath (bundleDir ++ "/registration-id") ≠ [seg])
    (hne_b3 : normalizePath (bundleDir ++ "/signed-pre-key") ≠ [seg])
    (hne_b4 : normalizePath (bundleDir ++ "/kyber-pre-key") ≠ [seg])
    (hne_coins : normalizePath coinsFile ≠ [seg])
    (hfile : runFiles (pqInitInputs P st zeroBundleInit t) seg = some (.file bs)) :
    bs.length ≤ 105 := by
  obtain ⟨p, hnorm, hmem⟩ := initFsState_files_mem_norm_init hfile
  have hnorm' : normalizePath p = [seg] := hnorm.trans hnorm_seg
  have hmem0 : (p, bs) ∈ (pqInitInputs P st zeroBundleInit t).files := hmem
  simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hmem0
  rcases hmem0 with (hed | hbun) | hcoins
  · unfold encodeDir at hed
    simp only [List.mem_append] at hed
    rcases hed with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
      rcases hf_hdr with h1 | h2 | h3
      · injection h1 with _ hbs; subst hbs
        exact Nat.le_trans (partyAddress_textBytes_length_le_40_init st.party) (by decide)
      · injection h2 with _ hbs; subst hbs
        exact identityKeyPair_encode_length_le_105_init P st.me
      · injection h3 with _ hbs; subst hbs
        exact (by rfl : (le32 st.me.regId).length = 4) ▸ (by decide : 4 ≤ 105)
    · cases hp : st.peerId with
      | none => simp [hp] at hf_peer
      | some k =>
        simp only [hp, List.mem_singleton] at hf_peer
        injection hf_peer with _ hbs; subst hbs
        have hk : k.serialize.length = 33 := by
          simp [CryptoGames.LibsignalSession.IdentityKey.serialize,
            CryptoGames.LibsignalSession.PublicKey.serialize]
        omega
    · simp [hs] at hf_sess
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨id, _⟩, _, hpEq⟩
      injection hpEq with hp1 _
      subst hp1
      exact absurd hnorm'
        (norm_dir_slash_ne_seg (dir := "signed-pre-keys") (by decide) (by decide) hne_sig)
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨id, _⟩, _, hpEq⟩
      injection hpEq with hp1 _
      subst hp1
      exact absurd hnorm'
        (norm_dir_slash_ne_seg (dir := "one-time-pre-keys") (by decide) (by decide) hne_ot)
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨id, _⟩, _, hpEq⟩
      injection hpEq with hp1 _
      subst hp1
      exact absurd hnorm'
        (norm_dir_slash_ne_seg (dir := "one-time-kyber-pre-keys") (by decide) (by decide) hne_kot)
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨l, hl, hmem_l⟩
      rw [List.mem_map] at hl
      rcases hl with ⟨⟨id, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem_l
      rcases hmem_l with hpEq | hpEq
      · injection hpEq with hp1 _; subst hp1
        exact absurd hnorm'
          (norm_dir_slash_ne_seg
            (dir := "last-resort-kyber-pre-keys") (by decide) (by decide) hne_klr)
      · injection hpEq with hp1 _; subst hp1
        unfold baseKeysFile at hnorm'
        rw [String.append_assoc] at hnorm'
        exact absurd hnorm'
          (norm_dir_slash_ne_seg
            (dir := "last-resort-kyber-pre-keys") (by decide) (by decide) hne_klr)
  · simp only [publicBundleOf, PublicBundle.files, zeroBundleInit, Option.map,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hbun
    rcases hbun with h1 | h2 | h3 | h4
    · injection h1 with hp1 _; subst hp1; exact absurd hnorm' hne_b1
    · injection h2 with hp1 _; subst hp1; exact absurd hnorm' hne_b2
    · injection h3 with hp1 _; subst hp1; exact absurd hnorm' hne_b3
    · injection h4 with hp1 _; subst hp1; exact absurd hnorm' hne_b4
  · injection hcoins with hp1 _; subst hp1; exact absurd hnorm' hne_coins

private theorem own_ikp_le_105_of_cliInitD3Inputs {P : PEParams} {i : Inputs}
    (hi : CliInitD3Inputs P i) :
    ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105 := by
  obtain ⟨st, files, t, _hwf, hs, hb, heq⟩ := hi
  have hrf := runFiles_eq_pqInitZero_of_nonBundleCoins heq hb "identity-key-pair" nonBundleCoins_ikp
  have hpth : pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
      "identity-key-pair" := pathStr_utf8_ikp
  intro bs hget
  change cliRd (runFiles i)
    (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hget
  have hnil_or_some : bs = [] ∨ runFiles i "identity-key-pair" = some (.file bs) := by
    unfold cliRd at hget
    split at hget
    · cases hget
    · rename_i rbs hrv; injection hget with h; subst h
      rw [hpth] at hrv
      unfold readViewF at hrv; split at hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl
      · split at hrv
        · rename_i fbs hfp
          split at hrv
          · injection hrv with h; subst h; exact Or.inr hfp
          · cases hrv
        · cases hrv
        · injection hrv with h; subst h; exact Or.inl rfl
  rcases hnil_or_some with rfl | hfile
  · exact Nat.zero_le 105
  · rw [hrf] at hfile
    exact pqInitZero_singleSeg_file_le_105 hs (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hfile

private theorem not_overCapFile_own_address_of_cliInitD3Inputs {P : PEParams} {i : Inputs}
    (hi : CliInitD3Inputs P i) :
    ¬ OverCapFile (runFiles i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) := by
  obtain ⟨st, files, t, _hwf, hs, hb, heq⟩ := hi
  have hrf := runFiles_eq_pqInitZero_of_nonBundleCoins heq hb "address" nonBundleCoins_address
  have hpth : pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) = "address" :=
    pathStr_utf8_address
  intro ⟨_, fbs, hfile, hgt⟩
  rw [hpth, hrf] at hfile
  have hle := pqInitZero_singleSeg_file_le_105 hs (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hfile
  omega

private theorem preEnv_fixed_eq_plain_initD3 {P : PEParams} {g : RunCall}
    (hi : CliInitD3Inputs P g.i) :
    PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
      PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
  funext evs
  unfold PreEnv cliRunCalleesEnvs
  dsimp only
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_own_address_of_cliInitD3Inputs hi)]

/-! ### 3c. Bounded-Read `.init` Arm Envelope & `RunEnv` Containment -/

private def R1bFileStepBoundedEnv (dir name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (OptStageEnv (PathEnv dir name))
    (SeqEnv (OptStageEnv BoundedReadFileEnv)
      (SeqEnv FreeOnlyEvs
        (OptStageEnv
          (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)))) evs

private abbrev R1bBoundedTail3 (dir : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepBoundedEnv dir (utf8 "one-time-pre-key")))
    (SeqEnv (OptStageEnv (SplitIdEnv [])) (OptStageEnv R1bDeserStageEnv))

private abbrev R1bBoundedTail2 (dir : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepBoundedEnv dir (utf8 "kyber-pre-key")))
    (SeqEnv (OptStageEnv (SplitSignedEnv [])) (R1bBoundedTail3 dir))

private abbrev R1bBoundedTail1 (dir : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (OptStageEnv (R1bFileStepBoundedEnv dir (utf8 "signed-pre-key")))
    (SeqEnv (OptStageEnv (SplitSignedEnv [])) (R1bBoundedTail2 dir))

private def R1bBinaryBoundedEnv (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv (R1bFileStepBoundedEnv dir (utf8 "registration-id")) (R1bBoundedTail1 dir) evs

private def W3SlotFixedEnv (g : RunCall) : List AllocEvent → Prop :=
  match g.c with
  | .init _ _ => fun evs =>
    ∃ w : W3BinaryInitParams,
      W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
  | _ => fun _ => False

private def InitArmCoreBoundedEnv (dir : List (BitVec 8)) (g : RunCall)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (R1bFileStepBoundedEnv dir (utf8 "identity-key"))
    (SeqEnv (OptStageEnv (R1bBinaryBoundedEnv dir))
      (OptStageEnv (R1cEnv (W3SlotFixedEnv g)))) evs

private def E_initD3 (g : RunCall) : CliRunCalleeEnvs where
  initEnv := InitArmCoreBoundedEnv (bytesOfString bundleDir) g
  encEnv := fun _ => False
  decSigEnv := fun _ => False
  pksmEnv := fun _ _ => False
  decPkEnv := fun _ => False

private theorem r1bFileStepBoundedEnv_append_freeOnly {dir name : List (BitVec 8)}
    {e₁ ef : List AllocEvent}
    (h₁ : R1bFileStepBoundedEnv dir name e₁) (hf : FreeOnlyEvs ef) :
    R1bFileStepBoundedEnv dir name (e₁ ++ ef) := by
  rcases h₁ with hp | ⟨ep, er, rfl, hp, hr⟩
  · exact Or.inr ⟨e₁, ef, rfl, hp, Or.inl (Or.inl hf)⟩
  · refine Or.inr ⟨ep, er ++ ef, List.append_assoc ep er ef, hp, ?_⟩
    rcases hr with hr0 | ⟨er0, et, rfl, hr0, ht⟩
    · exact Or.inr ⟨er, ef, rfl, hr0, Or.inl hf⟩
    · refine Or.inr ⟨er0, et ++ ef, List.append_assoc er0 et ef, hr0, ?_⟩
      rcases ht with hft | ⟨ef0, eu, rfl, hf0, hu⟩
      · exact Or.inl (freeOnlyEvs_append hft hf)
      · refine Or.inr ⟨ef0, eu ++ ef, List.append_assoc ef0 eu ef, hf0, ?_⟩
        rcases hu with hfu | hv
        · exact Or.inl (freeOnlyEvs_append hfu hf)
        · refine Or.inr ?_
          rcases hv with ha | ⟨ea, ef1, rfl, ha, hf1⟩
          · exact Or.inr ⟨eu, ef, rfl, ha, hf⟩
          · exact Or.inr ⟨ea, ef1 ++ ef, List.append_assoc ea ef1 ef, ha,
              freeOnlyEvs_append hf1 hf⟩

private theorem bundleReadFixed_sub_r1bFileStepBoundedEnv {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : PubBundleReadEnv cliIo.rd PathEnv (ReadFileRuleEnvFixed cliIo.rd) files dir name evs) :
    R1bFileStepBoundedEnv dir name evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  rcases h with hp | ⟨ep, et, rfl, hp, ht⟩
  · exact Or.inl (Or.inr hp)
  · rcases ht with hr | ⟨er, ea, rfl, hr, ha⟩
    · exact Or.inr ⟨ep, et, rfl, Or.inr hp,
        Or.inl (Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files _ et hr))⟩
    · refine Or.inr ⟨ep, er ++ ea, rfl, Or.inr hp,
        Or.inr ⟨er, ea, rfl,
          Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files _ er hr), ?_⟩⟩
      unfold BundleReadAfterReadEnv at ha
      cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ name) with
      | ok _ =>
        rw [hrd] at ha
        exact Or.inl ha
      | error _ =>
        rw [hrd] at ha
        exact Or.inr ⟨[], ea, rfl, hnil,
          Or.inr (seqEnv_mono_init (fun _ he => Or.inl he) (fun _ hf => hf) ha)⟩

private theorem rawReadFixed_sub_r1bFileStepBoundedEnv {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv (PathEnv dir name)
      (ReadFileRuleEnvFixed cliIo.rd files (dir ++ [0x2f#8] ++ name)) evs) :
    R1bFileStepBoundedEnv dir name evs := by
  rcases h with hp | ⟨ep, er, rfl, hp, hr⟩
  · exact Or.inl (Or.inr hp)
  · exact Or.inr ⟨ep, er, rfl, Or.inr hp,
      Or.inl (Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files _ er hr))⟩

private theorem rawReadFreeFixed_sub_r1bFileStepBoundedEnv {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv
      (SeqEnv (PathEnv dir name) (ReadFileRuleEnvFixed cliIo.rd files (dir ++ [0x2f#8] ++ name)))
      FreeOnlyEvs evs) :
    R1bFileStepBoundedEnv dir name evs := by
  rcases h with hpr | ⟨epr, ef, rfl, hpr, hf⟩
  · exact rawReadFixed_sub_r1bFileStepBoundedEnv hpr
  · exact r1bFileStepBoundedEnv_append_freeOnly (rawReadFixed_sub_r1bFileStepBoundedEnv hpr) hf

private theorem rawReadFree_append_errFixed_sub_r1bFileStepBoundedEnv {files : FsFiles}
    {dir name : List (BitVec 8)} {evs : List AllocEvent}
    (h : SeqEnv
      (SeqEnv
        (SeqEnv (PathEnv dir name) (ReadFileRuleEnvFixed cliIo.rd files (dir ++ [0x2f#8] ++ name)))
        FreeOnlyEvs)
      (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs) evs) :
    R1bFileStepBoundedEnv dir name evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  rcases h with hrf | ⟨erf, ee, rfl, hrf, hee⟩
  · exact rawReadFreeFixed_sub_r1bFileStepBoundedEnv hrf
  · rcases hrf with hpr | ⟨epr, ef, rfl, hpr, hf⟩
    · rcases hpr with hp | ⟨ep, er, rfl, hp, hr⟩
      · exact Or.inr ⟨erf, ee, rfl, Or.inr hp,
          Or.inr ⟨[], ee, rfl, Or.inl hnil, Or.inr ⟨[], ee, rfl, hnil, Or.inr hee⟩⟩⟩
      · exact Or.inr ⟨ep, er ++ ee, List.append_assoc ep er ee, Or.inr hp,
          Or.inr ⟨er, ee, rfl,
            Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files _ er hr),
            Or.inr ⟨[], ee, rfl, hnil, Or.inr hee⟩⟩⟩
    · rcases hpr with hp | ⟨ep, er, rfl, hp, hr⟩
      · exact Or.inr ⟨epr, ef ++ ee, List.append_assoc epr ef ee, Or.inr hp,
          Or.inr ⟨[], ef ++ ee, rfl, Or.inl hnil, Or.inr ⟨ef, ee, rfl, hf, Or.inr hee⟩⟩⟩
      · rw [List.append_assoc ep er ef, List.append_assoc ep (er ++ ef) ee,
          List.append_assoc er ef ee]
        exact Or.inr ⟨ep, er ++ (ef ++ ee), rfl, Or.inr hp,
          Or.inr ⟨er, ef ++ ee, rfl,
            Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo files _ er hr),
            Or.inr ⟨ef, ee, rfl, hf, Or.inr hee⟩⟩⟩

private theorem init2Stage3Fixed_sub_r1bBoundedTail3 {files : FsFiles}
    {dir spkKey kpkKey : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2Stage3Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      files dir spkKey kpkKey evs) :
    R1bBoundedTail3 dir evs := by
  let cEnvs := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hbSub : ∀ {e}, cEnvs.bundleRead files dir (utf8 "one-time-pre-key") e →
      R1bFileStepBoundedEnv dir (utf8 "one-time-pre-key") e := fun he =>
    bundleReadFixed_sub_r1bFileStepBoundedEnv he
  have hsidSub : ∀ {b e}, cEnvs.splitId b e → SplitIdEnv [] e := fun he =>
    pubSplitIdEnv_sub_splitIdEnv he
  have hopkSplitFree : ∀ {b} {e},
      SeqEnv (SeqEnv (cEnvs.bundleRead files dir (utf8 "one-time-pre-key")) (cEnvs.splitId b))
        FreeOnlyEvs e →
      R1bBoundedTail3 dir e := by
    intro b e hs0
    rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inr ⟨eb, es, rfl, Or.inr (hbSub hb), Or.inl (Or.inr (hsidSub hsi))⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
      · exact Or.inl (Or.inr (r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf))
      · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef, Or.inr (hbSub hb),
          Or.inl (Or.inr (splitIdEnv_append_freeOnly (hsidSub hsi) hf))⟩
  rcases h with hb | herr | hm
  · exact Or.inl (Or.inr (hbSub hb))
  · unfold R1bStepOpkErrEnv at herr
    cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
    | error _ =>
      rw [hrd] at herr
      rcases herr with hb | ⟨eb, ef, rfl, hb, hf⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inl (Or.inr (r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf))
    | ok opkBs =>
      rw [hrd] at herr
      cases opkBs with
      | nil => exact False.elim herr
      | cons b bs =>
        dsimp only at herr
        cases hsp : splitId (b :: bs) with
        | none => rw [hsp] at herr; exact hopkSplitFree herr
        | some p =>
          rw [hsp] at herr; dsimp only at herr
          split at herr
          · exact hopkSplitFree herr
          · exact False.elim herr
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "one-time-pre-key") with
    | error _ => rw [hrd] at hm; exact False.elim hm
    | ok opkBs =>
      rw [hrd] at hm
      cases opkBs with
      | nil =>
        have hokNil : ∀ {e}, R1bStepOpkOkEnv cEnvs files dir [] e →
            R1bFileStepBoundedEnv dir (utf8 "one-time-pre-key") e := by
          intro e he
          unfold R1bStepOpkOkEnv at he
          simp only [List.isEmpty_nil, ↓reduceIte] at he
          rcases he with hb | ⟨eb, ef, rfl, hb, hf⟩
          · exact hbSub hb
          · exact r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf
        rcases hm with hok | ⟨eok, e4, rfl, hok, h4⟩
        · exact Or.inl (Or.inr (hokNil hok))
        · exact Or.inr ⟨eok, e4, rfl, Or.inr (hokNil hok),
            Or.inr ⟨[], e4, rfl, Or.inl hnil, init2Stage4Env_sub_r1bDeserStageEnv h4⟩⟩
      | cons b bs =>
        rcases hm with hbs | hm2
        · exact hopkSplitFree (Or.inl hbs)
        · split at hm2
          · exact False.elim hm2
          · split at hm2
            · exact False.elim hm2
            · unfold R1bStepOpkOkEnv at hm2
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hm2
              rcases hm2 with hok | ⟨eok, e4, rfl, hok, h4⟩
              · exact hopkSplitFree hok
              · have h4' := init2Stage4Env_sub_r1bDeserStageEnv h4
                rcases hok with hs | ⟨ebs, ef, rfl, hs, hf⟩
                · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
                  · exact Or.inr ⟨eok, e4, rfl, Or.inr (hbSub hb),
                      Or.inr ⟨[], e4, rfl, Or.inl hnil, h4'⟩⟩
                  · exact Or.inr ⟨eb, es ++ e4, List.append_assoc eb es e4, Or.inr (hbSub hb),
                      Or.inr ⟨es, e4, rfl, Or.inr (hsidSub hsi), h4'⟩⟩
                · rcases hs with hb | ⟨eb, es, rfl, hb, hsi⟩
                  · exact Or.inr ⟨ebs ++ ef, e4, rfl,
                      Or.inr (r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf),
                      Or.inr ⟨[], e4, rfl, Or.inl hnil, h4'⟩⟩
                  · rw [List.append_assoc eb es ef, List.append_assoc eb (es ++ ef) e4]
                    exact Or.inr ⟨eb, (es ++ ef) ++ e4, rfl, Or.inr (hbSub hb),
                      Or.inr ⟨es ++ ef, e4, rfl,
                        Or.inr (splitIdEnv_append_freeOnly (hsidSub hsi) hf), h4'⟩⟩

private theorem init2Stage2Fixed_sub_r1bBoundedTail2 {files : FsFiles}
    {dir spkKey : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2Stage2Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      files dir spkKey evs) :
    R1bBoundedTail2 dir evs := by
  let cEnvs := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hbSub : ∀ {e}, cEnvs.bundleRead files dir (utf8 "kyber-pre-key") e →
      R1bFileStepBoundedEnv dir (utf8 "kyber-pre-key") e := fun he =>
    bundleReadFixed_sub_r1bFileStepBoundedEnv he
  have hssgSub : ∀ {b e}, cEnvs.splitSigned b e → SplitSignedEnv [] e := fun he =>
    pubSplitSignedEnv_sub_splitSignedEnv he
  have hkpkFree : ∀ {b e}, SeqEnv (R1bStepKpkOkEnv cEnvs files dir b) FreeOnlyEvs e →
      R1bBoundedTail2 dir e := by
    intro b e hs0
    rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hss⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inr ⟨eb, es, rfl, Or.inr (hbSub hb), Or.inl (Or.inr (hssgSub hss))⟩
    · rcases hs with hb | ⟨eb, es, rfl, hb, hss⟩
      · exact Or.inl (Or.inr (r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf))
      · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef, Or.inr (hbSub hb),
          Or.inl (Or.inr (splitSignedEnv_append_freeOnly (hssgSub hss) hf))⟩
  rcases h with hb | herr | hm
  · exact Or.inl (Or.inr (hbSub hb))
  · unfold R1bStepKpkErrEnv at herr
    cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
    | error _ =>
      rw [hrd] at herr
      rcases herr with hb | ⟨eb, ef, rfl, hb, hf⟩
      · exact Or.inl (Or.inr (hbSub hb))
      · exact Or.inl (Or.inr (r1bFileStepBoundedEnv_append_freeOnly (hbSub hb) hf))
    | ok kpkBs =>
      rw [hrd] at herr
      exact hkpkFree herr.2
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "kyber-pre-key") with
    | error _ => rw [hrd] at hm; exact False.elim hm
    | ok kpkBs =>
      rw [hrd] at hm
      rcases hm with hok | hm2
      · exact hkpkFree (Or.inl hok)
      · split at hm2
        · exact False.elim hm2
        · rcases hm2 with hok | ⟨eok, e3, rfl, hok, h3⟩
          · exact hkpkFree (Or.inl hok)
          · have h3' := init2Stage3Fixed_sub_r1bBoundedTail3 h3
            rcases hok with hb | ⟨eb, es, rfl, hb, hss⟩
            · exact Or.inr ⟨eok, e3, rfl, Or.inr (hbSub hb),
                Or.inr ⟨[], e3, rfl, Or.inl hnil, h3'⟩⟩
            · exact Or.inr ⟨eb, es ++ e3, List.append_assoc eb es e3, Or.inr (hbSub hb),
                Or.inr ⟨es, e3, rfl, Or.inr (hssgSub hss), h3'⟩⟩

private theorem init2AfterRegOkFixed_sub_r1bBoundedTail1 {files : FsFiles}
    {dir : List (BitVec 8)} {evs : List AllocEvent}
    (h : Init2AfterRegOkEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) files dir evs) :
    R1bBoundedTail1 dir evs := by
  let cEnvs := cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  have hssgSub : ∀ {b e}, cEnvs.splitSigned b e → SplitSignedEnv [] e := fun he =>
    pubSplitSignedEnv_sub_splitSignedEnv he
  unfold Init2AfterRegOkEnv at h
  dsimp only [cliRunCalleesEnvs] at h
  rcases h with hp | hpr | hm
  · exact Or.inl (Or.inr (Or.inl (Or.inr hp)))
  · exact Or.inl (Or.inr (rawReadFixed_sub_r1bFileStepBoundedEnv hpr))
  · cases hrd : cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "signed-pre-key") with
    | error _ =>
      rw [hrd] at hm
      exact Or.inl (Or.inr (rawReadFree_append_errFixed_sub_r1bFileStepBoundedEnv
        (seqEnv_mono_init (fun _ h1 => Or.inl h1)
          (fun _ h2 => seqEnv_mono_init (fun _ he => Or.inl he) (fun _ hf => hf) h2) hm)))
    | ok spkBs =>
      rw [hrd] at hm
      dsimp only at hm
      have hspkFree : ∀ {e},
          SeqEnv (SeqEnv
            (SeqEnv (SeqEnv (PathEnv dir (utf8 "signed-pre-key"))
              (ReadFileRuleEnvFixed cliIo.rd files (dir ++ [0x2f#8] ++ utf8 "signed-pre-key")))
              FreeOnlyEvs)
            (cEnvs.splitSigned spkBs)) FreeOnlyEvs e →
          R1bBoundedTail1 dir e := by
        intro e hs0
        rcases hs0 with hs | ⟨ebs, ef, rfl, hs, hf⟩
        · rcases hs with hr | ⟨eb, es, rfl, hr, hss⟩
          · exact Or.inl (Or.inr (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr))
          · exact Or.inr ⟨eb, es, rfl, Or.inr (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr),
              Or.inl (Or.inr (hssgSub hss))⟩
        · rcases hs with hr | ⟨eb, es, rfl, hr, hss⟩
          · exact Or.inl (Or.inr (r1bFileStepBoundedEnv_append_freeOnly
              (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr) hf))
          · exact Or.inr ⟨eb, es ++ ef, List.append_assoc eb es ef,
              Or.inr (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr),
              Or.inl (Or.inr (splitSignedEnv_append_freeOnly (hssgSub hss) hf))⟩
      rcases hm with hok | hm2
      · exact hspkFree (Or.inl hok)
      · split at hm2
        · exact hspkFree hm2
        · rcases hm2 with hok | ⟨eok, e2, rfl, hok, h2⟩
          · exact hspkFree (Or.inl hok)
          · have h2' := init2Stage2Fixed_sub_r1bBoundedTail2 h2
            rcases hok with hr | ⟨eb, es, rfl, hr, hss⟩
            · exact Or.inr ⟨eok, e2, rfl, Or.inr (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr),
                Or.inr ⟨[], e2, rfl, Or.inl hnil, h2'⟩⟩
            · exact Or.inr ⟨eb, es ++ e2, List.append_assoc eb es e2,
                Or.inr (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr),
                Or.inr ⟨es, e2, rfl, Or.inr (hssgSub hss), h2'⟩⟩

private theorem init2Fixed_sub_r1bBinaryBoundedEnv (g : RunCall) (d : Init1Data)
    {evs : List AllocEvent}
    (h : Init2Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g d evs) :
    R1bBinaryBoundedEnv d.dir evs := by
  unfold Init2Env at h
  dsimp only [cliRunCalleesEnvs] at h
  rcases h with hp | hpr | hm
  · exact Or.inl (Or.inl (Or.inr hp))
  · exact Or.inl (rawReadFixed_sub_r1bFileStepBoundedEnv hpr)
  · cases hrd : cliIo.rd (runFiles g.i) (d.dir ++ [0x2f#8] ++ utf8 "registration-id") with
    | error _ =>
      rw [hrd] at hm
      exact Or.inl (rawReadFree_append_errFixed_sub_r1bFileStepBoundedEnv
        (seqEnv_mono_init (fun _ h1 => Or.inl h1)
          (fun _ h2 => seqEnv_mono_init (fun _ he => Or.inl he) (fun _ hf => hf) h2) hm))
    | ok regBs =>
      rw [hrd] at hm
      dsimp only at hm
      split at hm
      · rcases hm with hr | ⟨er, e1, rfl, hr, h1⟩
        · exact Or.inl (rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr)
        · exact Or.inr ⟨er, e1, rfl, rawReadFreeFixed_sub_r1bFileStepBoundedEnv hr,
            init2AfterRegOkFixed_sub_r1bBoundedTail1 h1⟩
      · exact Or.inl (rawReadFree_append_errFixed_sub_r1bFileStepBoundedEnv
          (seqEnv_mono_init (fun _ h1 => h1)
            (fun _ h2 => seqEnv_mono_init (fun _ he => Or.inr he) (fun _ hf => hf) h2) hm))

private theorem init1Fixed_sub_r1bFileStepBoundedEnv
    (g : RunCall) (me : MeAtDispatch) (peerV : AddrV) (dir : List (BitVec 8))
    {evs : List AllocEvent}
    (h : Init1Env (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g me peerV dir evs) :
    R1bFileStepBoundedEnv dir (utf8 "identity-key") evs := by
  cases me with
  | none => exact Or.inl (Or.inl h)
  | some _ _ =>
    dsimp only [Init1Env, cliRunCalleesEnvs] at h
    rcases h with hp | ⟨ep, er, hp, hr, rfl⟩ | ⟨ep, er, et, hp, hr, ht, rfl⟩
    · exact Or.inl (Or.inr hp)
    · exact Or.inr ⟨ep, er, rfl, Or.inr hp,
        Or.inl (Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo (runFiles g.i) _ er hr))⟩
    · refine Or.inr ⟨ep, er ++ et, List.append_assoc ep er et, Or.inr hp,
        Or.inr ⟨er, et, rfl,
          Or.inr (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo (runFiles g.i) _ er hr), ?_⟩⟩
      unfold Init1AfterReadEnv at ht
      split at ht
      · obtain ⟨ef, hf, rfl⟩ := ht
        exact Or.inr ⟨[], rustAllocEvents 22 1 ++ ef, rfl,
          fun _ hm => False.elim (List.not_mem_nil hm),
          Or.inr (Or.inr ⟨rustAllocEvents 22 1, ef, rfl, Or.inl rfl, hf⟩)⟩
      · exact Or.inl ht

private theorem w3_realCliInitSlotFixed_sub_w3SlotFixed [LibsignalPlacement]
    (W : CliHooks) (g : RunCall) (peerV : AddrV) (dir : List (BitVec 8)) (d2 : Init2Data)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hc : g.c = .init peerV dir)
    (hpeerVal : d2.peerG.val = addrValOf peerV)
    {evs : List AllocEvent}
    (hevs : realCliInitBinarySlotEnvFixed W (r1cInitGhost g d2 0#64) evs) :
    W3SlotFixedEnv g evs := by
  obtain ⟨w, hx, _hF, hspqr, hgv, halice, hslotF⟩ := hevs
  have hparse_init : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.init peerV dir) :=
    hc ▸ hparse
  have hp40 : peerV.name.length ≤ 40 := parseArgs_peer_name_length_le hparse_init
  have hdom : W3BinaryInitDom g.c g.i w := by
    intro pV d hc'
    rcases CallV.init.inj (hc.symm.trans hc') with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, hspqr, hgv, halice⟩
    · rw [hx]; exact hpeerVal
    · change w.x.peer.val.name.length ≤ 40
      rw [hx]
      dsimp only [r1cInitGhost]
      rw [hpeerVal]
      exact hp40
    · rw [hx]; rfl
  unfold W3SlotFixedEnv
  rw [hc]
  exact ⟨w, hc ▸ hdom, hslotF⟩

private theorem initArmCoreBounded_sub_initArmBinaryEnv (g : RunCall)
    {evs : List AllocEvent}
    (h : InitArmCoreBoundedEnv (bytesOfString bundleDir) g evs) :
    InitArmBinaryEnv cliIo.rd (runFiles g.i) (bytesOfString bundleDir) (E_initD3 g).initEnv evs := by
  have hnil : FreeOnlyEvs [] := fun _ hm => nomatch hm
  exact Or.inr (Or.inr ⟨[], evs, rfl, Or.inl (Or.inl hnil),
    Or.inr ⟨[], evs, rfl, Or.inl hnil, Or.inr (Or.inl h)⟩⟩)

private theorem runEnvFixed_sub_cliRunBinaryEnv_initD3 [LibsignalPlacement]
    {M : AllocCostModel}
    (S : RunSem) (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (g : RunCall)
    (hi : CliInitD3Inputs ⟨W.C, W.Q⟩ g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    ∀ evs,
      RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S)
        g evs →
      CliRunBinaryEnv cliIo.rd (E_initD3 g) sessionCapBytes g evs := by
  let aEnvs := cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
    (binaryKitRunSlotEnvsFixed W A B (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
    PksmTryFromEnv S
  obtain ⟨st, files, t, hwf, hs, hb, heq⟩ := hi
  have hi' : CliInitD3Inputs ⟨W.C, W.Q⟩ g.i := ⟨st, files, t, hwf, hs, hb, heq⟩
  have hargv_eq : g.i.argv = ["init", (partyAddress st.party.other).text, bundleDir] := heq.1
  have hparse_b : parseArgs uuidTryParse
      ([bytesOfString "init", bytesOfString (partyAddress st.party.other).text,
        bytesOfString bundleDir]) = some g.c := by
    simpa only [hargv_eq, List.map_cons, List.map_nil] using hparse
  obtain ⟨peerV0, hc0⟩ := parseArgs_init_bundleDir_init hparse_b
  have hpre : ∀ evs, aEnvs.pre g evs → R0BinaryEnv cliIo.rd g evs := fun _ hp =>
    preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
      (Eq.mp (congrFun (preEnv_fixed_eq_plain_initD3 hi') _) hp)
  have harmAtMe : ∀ me evs, RunArmAtMeEnv aEnvs g me evs →
      RunArmBinaryEnv cliIo.rd (runFiles g.i) (E_initD3 g) sessionCapBytes g.i.stdin g.c evs := by
    intro me evs ha
    unfold RunArmAtMeEnv at ha
    rw [hc0] at ha ⊢
    dsimp only [RunArmBinaryEnv]
    apply initArmCoreBounded_sub_initArmBinaryEnv g
    cases me with
    | none =>
      exact Or.inl (init1Fixed_sub_r1bFileStepBoundedEnv g .none peerV0 (bytesOfString bundleDir) ha)
    | some meV meG =>
      refine seqEnv_mono_init
        (fun _ h1 => init1Fixed_sub_r1bFileStepBoundedEnv g (.some meV meG) peerV0
          (bytesOfString bundleDir) h1)
        (fun ec hc => ?_) ha
      unfold RunInit2ChainEnv at hc
      split at hc
      · exact False.elim hc
      · split at hc
        · exact False.elim hc
        · obtain ⟨d1, _, hd1_dir, _, _, _, _, _, hseq23⟩ := hc
          refine seqEnv_mono_init
            (fun _ h2 => Or.inr (hd1_dir ▸ init2Fixed_sub_r1bBinaryBoundedEnv g d1 h2))
            (fun e3 h3 => ?_) hseq23
          unfold RunInit3Env at h3
          split at h3
          · exact False.elim h3
          · obtain ⟨d2, _, _, _, _, hd2_pv, _, _, _, _, hi3⟩ := h3
            exact Or.inr (r1cInit3Env_sub_r1cEnv
              (fun e1 hs1 => w3_realCliInitSlotFixed_sub_w3SlotFixed W g peerV0
                (bytesOfString bundleDir) d2 hparse hc0 hd2_pv hs1)
              hi3)
  have hdisp : ∀ evs, RunDispatchEnv aEnvs g evs →
      RunArmBinaryEnv cliIo.rd (runFiles g.i) (E_initD3 g) sessionCapBytes g.i.stdin g.c evs := by
    intro evs hd
    unfold RunDispatchEnv at hd
    split at hd
    · exact False.elim hd
    · split at hd
      · exact harmAtMe .none evs hd
      · obtain ⟨meG, _, _, _, ha⟩ := hd
        exact harmAtMe (.some _ meG) evs ha
  have hcore : ∀ evs, RunCoreEnv aEnvs g evs →
      CliRunBinaryEnv cliIo.rd (E_initD3 g) sessionCapBytes g evs := by
    intro evs hc
    rcases hc with he0 | ⟨e0, e1, rfl, he0, he1⟩
    · exact Or.inr (Or.inl (hpre evs he0))
    · exact Or.inr (Or.inr ⟨e0, e1, rfl, hpre e0 he0, Or.inl (hdisp e1 he1)⟩)
  intro evs hrun
  rcases hrun with hc | ⟨ec, ef, rfl, hc, hf⟩
  · exact hcore evs hc
  · rcases hcore ec hc with hf0 | hr0 | ⟨e0, eaj, rfl, hr0, haj⟩
    · exact Or.inl (freeOnlyEvs_append hf0 hf)
    · have hnil : RunArmBinaryEnv cliIo.rd (runFiles g.i) (E_initD3 g)
          sessionCapBytes g.i.stdin g.c [] :=
        runArmEnv_sub_runArmBinaryEnv
          (runArmEnv_nil cliIo.rd (runFiles g.i) (E_initD3 g) sessionCapBytes g.i.stdin g.c)
      exact Or.inr (Or.inr ⟨ec, ef, rfl, hr0, Or.inr ⟨[], ef, rfl, hnil, hf⟩⟩)
    · refine Or.inr (Or.inr ⟨e0, eaj ++ ef, List.append_assoc e0 eaj ef, hr0, ?_⟩)
      rcases haj with ha | ⟨ea, ej, rfl, ha, hj⟩
      · exact Or.inr ⟨eaj, ef, rfl, ha, hf⟩
      · exact Or.inr ⟨ea, ej ++ ef, List.append_assoc ea ej ef, ha, freeOnlyEvs_append hj hf⟩

/-! ### 3d. `PhaseCreditSpec`, `PhaseGroupSpec`, and `1 GiB` Whole-`main` `FitsEnv` for `E_initD3` -/

private theorem optStage_phaseCredit_init {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem optStage_groupSpec_init {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem fine_sm_bounds_init :
    131072 ≤ HasFineReallocCredit.smallMaxReq fineCostModel ∧
    HasFineReallocCredit.smallMaxReq fineCostModel < 262144 := by
  rw [fineCostModel_smallMaxReq_eq]; decide

private theorem boundedReadFile_phaseCredit_init :
    PhaseCreditSpec fineCostModel BoundedReadFileEnv
      (fineReadFileCum sessionCapBytes)
      (fineReadFileLive sessionCapBytes)
      (fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) := by
  have hM := fineCostModel_modelHyps
  have hb1 (bs : List (BitVec 8)) (hbs : bs.length ≤ sessionCapBytes) :
      PhaseCreditSpec fineCostModel (fun evs => evs = allocBytes1Events bs)
        readFileDeltaCum_tight (sessionCapBytes + 8195) 3162118 sessionCapBytes :=
    (phaseCredit_allocBytes1_tight hM fine_sm_bounds_init.2 bs hbs).mono
      (by unfold readFileDeltaCum_tight; decide)
      (Nat.le_refl _)
      (by unfold sessionCapBytes; decide)
      (Nat.le_refl _)
  have h1 : PhaseCreditSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ sessionCapBytes ∧ evs = allocBytes1Events bs)
      readFileDeltaCum_tight (sessionCapBytes + 8195) 3162118 sessionCapBytes :=
    { req_align := fun evs ⟨bs, hbs, he⟩ ev hev => (hb1 bs hbs).req_align evs he ev hev
      credit_le := fun st0 {_} ⟨bs, hbs, he⟩ => (hb1 bs hbs).credit_le st0 he }
  have hcap_raw : PhaseCreditSpec fineCostModel
      (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 573818 2105347 3162118 2097152 :=
    PhaseCreditSpec.of_imp (fun _ ⟨r, he⟩ => ⟨r, he⟩)
      (phaseCreditSpec_cliIoReadFile_anyR_tight hM fine_sm_bounds_init.1 fine_sm_bounds_init.2)
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (h1.or (hcap_raw.seq (PhaseCreditSpec.freeOnly hM.freeNonInc)))).mono
    (by unfold readFileDeltaCum_tight fineReadFileCum sessionCapBytes; decide)
    (by unfold fineReadFileLive sessionCapBytes; decide)
    (by unfold fineReadFilePeak sessionCapBytes; decide)
    (by unfold fineReadFileMaxReq sessionCapBytes; decide)

private theorem boundedReadFile_groupSpec_init :
    PhaseGroupSpec fineCostModel BoundedReadFileEnv (30 * FineScale) := by
  have h1 : PhaseGroupSpec fineCostModel
      (fun evs => ∃ bs : List (BitVec 8), bs.length ≤ sessionCapBytes ∧ evs = allocBytes1Events bs)
      (30 * FineScale) :=
    { groups_le := fun st0 {_} ⟨bs, _, hevs⟩ => by
        subst hevs; unfold allocBytes1Events; split
        · simp [AllocCostModel.stepEvents_nil]
        · exact Nat.le_trans
            ((PhaseGroupSpec.rustAlloc_any fineCostModel bs.length 1).groups_le st0 rfl)
            (Nat.add_le_add_left (by unfold FineScale; decide : 3 * FineScale ≤ 30 * FineScale) _) }
  have hnf : NonFreeBound (fun e => ∃ r : Nat, e = cliIoCapEvents (cliIoReadCaps 9 r)) 10 :=
    fun _ ⟨r, hr⟩ => hr ▸ cliIoReadFileEnv_nonFreeBound r _ rfl
  exact ((PhaseGroupSpec.nil fineCostModel).or
    (h1.or ((PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).seq
      (PhaseGroupSpec.freeOnly fineCostModel)))).mono (by unfold FineScale; decide)

private def r1bStepBoundedCum : Nat :=
  21185 + fineReadFileCum sessionCapBytes + (2 * 22 + 9539)

private theorem r1bFileStepBounded_phaseCredit {dir name : List (BitVec 8)}
    (hdir : dir.length ≤ 26) (hname : name.length ≤ 16) :
    PhaseCreditSpec fineCostModel (R1bFileStepBoundedEnv dir name)
      r1bStepBoundedCum
      (fineReadFileLive sessionCapBytes)
      (fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) := by
  have hp := optStage_phaseCredit_init
    (pathEnv_fine_phaseCredit_tight (Nat.le_trans hdir (by decide)) (Nat.le_trans hname (by decide)))
  have hr := optStage_phaseCredit_init boundedReadFile_phaseCredit_init
  have hsm22 : 22 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha22 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 22 1) (2 * 22 + 9539) 0 0 22 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 22) (al := 1) (by decide) hsm22).mono
      (fineCostModel_modelHyps.smallAlloc_le hsm22) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22)
  have ha14 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 14 1) (2 * 22 + 9539) 0 0 22 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 14) (al := 1) (by decide) hsm14).mono
      (Nat.le_trans (fineCostModel_modelHyps.smallAlloc_le hsm14) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (by decide : 14 ≤ 22)
  have herr : PhaseCreditSpec fineCostModel
      (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) (2 * 22 + 9539) 0 0 22 :=
    (ha22.or ha14).mono
      (max_self_le_init _) (max_self_le_init _) (max_self_le_init _) (max_self_le_init _)
  have htail := phaseCredit_seq_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
    (optStage_phaseCredit_init
      (phaseCredit_seq_freeOnly_right fineCostModel_modelHyps herr (fun _ hf => hf) (Nat.le_refl 0)))
  exact (hp.seq (hr.seq htail)).mono
    (by unfold r1bStepBoundedCum; omega) (by decide) (by decide) (by decide)

private theorem pathEnv_groupSpec_init (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (PathEnv dir name) (9 * FineScale) := by
  unfold PathEnv pathEvents
  have h1 : PhaseGroupSpec fineCostModel (· = pathToOwnedEvents dir.length) (3 * FineScale) := by
    unfold pathToOwnedEvents; split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel dir.length 1
  have h2 : PhaseGroupSpec fineCostModel (· = pathPushSlashEvents dir.length) (3 * FineScale) := by
    unfold pathPushSlashEvents; split
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel _ 1
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
  have h3 : PhaseGroupSpec fineCostModel (· = pathAppendNameEvents dir.length name.length)
      (3 * FineScale) := by
    unfold pathAppendNameEvents; dsimp only; split
    · exact PhaseGroupSpec.rustRealloc_any fineCostModel _ _ 1
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  exact (phaseGroupSpec_append_eq fineCostModel h1
    (phaseGroupSpec_append_eq fineCostModel h2 h3)).mono (by generalize FineScale = fs; omega)

private theorem r1bFileStepBounded_groupSpec (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1bFileStepBoundedEnv dir name) (42 * FineScale) := by
  have hp := optStage_groupSpec_init (pathEnv_groupSpec_init dir name)
  have hr := optStage_groupSpec_init boundedReadFile_groupSpec_init
  have herr : PhaseGroupSpec fineCostModel
      (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) (3 * FineScale) :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel 22 1).or
      (PhaseGroupSpec.rustAlloc_any fineCostModel 14 1)).mono (max_self_le_init _)
  have herrFree : PhaseGroupSpec fineCostModel
      (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)
      (3 * FineScale) :=
    (herr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  have htail : PhaseGroupSpec fineCostModel
      (SeqEnv FreeOnlyEvs
        (OptStageEnv
          (SeqEnv (fun e => e = rustAllocEvents 22 1 ∨ e = rustAllocEvents 14 1) FreeOnlyEvs)))
      (3 * FineScale) :=
    ((PhaseGroupSpec.freeOnly fineCostModel).seq (optStage_groupSpec_init herrFree)).mono
      (by generalize FineScale = fs; omega)
  exact (hp.seq (hr.seq htail)).mono (by generalize FineScale = fs; omega)

private theorem r1bFileStepPlain_phaseCredit {files : FsFiles} {dir name : List (BitVec 8)}
    (hdir : dir.length ≤ 26) (hname : name.length ≤ 16) :
    PhaseCreditSpec fineCostModel (R1bFileStepEnv cliIo.rd files dir name)
      r1bStepBoundedCum
      (fineReadFileLive sessionCapBytes)
      (fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) := by
  refine PhaseCreditSpec.of_imp (fun evs h => ?_) (r1bFileStepBounded_phaseCredit hdir hname)
  exact seqEnv_mono_init (fun _ hp => hp)
    (fun _ hr => seqEnv_mono_init
      (fun _ hr0 => match hr0 with
        | Or.inl hf => Or.inl hf
        | Or.inr hrr => Or.inr (boundedReadFileEnv_of_readFileRuleEnv_cliIo files _ hrr))
      (fun _ ht => ht) hr) h

private theorem r1bFileStepPlain_groupSpec (files : FsFiles) (dir name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (R1bFileStepEnv cliIo.rd files dir name) (42 * FineScale) := by
  refine { groups_le := fun st0 {_} h => (r1bFileStepBounded_groupSpec dir name).groups_le st0 ?_ }
  exact seqEnv_mono_init (fun _ hp => hp)
    (fun _ hr => seqEnv_mono_init
      (fun _ hr0 => match hr0 with
        | Or.inl hf => Or.inl hf
        | Or.inr hrr => Or.inr (boundedReadFileEnv_of_readFileRuleEnv_cliIo files _ hrr))
      (fun _ ht => ht) hr) h

private theorem r1bDeserStage_phaseCredit_init :
    PhaseCreditSpec fineCostModel R1bDeserStageEnv r1bDeserStageCum 0 0 kemPkLen := by
  have hsm64 : 64 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hsmKem : kemPkLen ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha64 := optStage_phaseCredit_init
    ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := 64) (al := 1) (by decide) hsm64).mono
      (fineCostModel_modelHyps.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64))
  have haKem := optStage_phaseCredit_init
    ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := kemPkLen) (al := 1) (by decide) hsmKem).mono
      (fineCostModel_modelHyps.smallAlloc_le hsmKem) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.le_refl kemPkLen))
  have ha64Free := optStage_phaseCredit_init
    (phaseCredit_seq_freeOnly_right fineCostModel_modelHyps
      ((PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
        (req := 64) (al := 1) (by decide) hsm64).mono
        (fineCostModel_modelHyps.smallAlloc_le hsm64) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 64))
      (fun _ hf => hf) (Nat.le_refl 0))
  exact (ha64.seq (haKem.seq ha64Free)).mono
    (by unfold r1bDeserStageCum; omega) (by decide) (by decide) (by decide)

private theorem r1bDeserStage_groupSpec_init :
    PhaseGroupSpec fineCostModel R1bDeserStageEnv (9 * FineScale) := by
  have ha64 := optStage_groupSpec_init (PhaseGroupSpec.rustAlloc_any fineCostModel 64 1)
  have haKem := optStage_groupSpec_init (PhaseGroupSpec.rustAlloc_any fineCostModel kemPkLen 1)
  have ha64Seq : PhaseGroupSpec fineCostModel
      (SeqEnv (· = rustAllocEvents 64 1) FreeOnlyEvs) (3 * FineScale) :=
    ((PhaseGroupSpec.rustAlloc_any fineCostModel 64 1).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)
  exact (ha64.seq (haKem.seq (optStage_groupSpec_init ha64Seq))).mono
    (by generalize FineScale = fs; omega)

private theorem splitId_groupSpec_init (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitIdEnv bs) (3 * FineScale) :=
  ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by generalize FineScale = fs; omega)

private theorem splitSigned_groupSpec_init (bs : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (SplitSignedEnv bs) (6 * FineScale) := by
  have h1 := splitId_groupSpec_init bs
  exact (h1.seq (optStage_groupSpec_init h1)).mono (by generalize FineScale = fs; omega)

private def w3FixedCum : Nat := w3InitRealCum + 4500000
private def w3FixedLive : Nat := w3InitRealLive + 65536
private def w3FixedPeak : Nat := w3InitRealPeak + 65536
private def w3FixedMaxReq : Nat := w3InitRealMaxReq + 65536
private def w3FixedGrpS : Nat := w3InitRealGrpS + 1500 * FineScale

private theorem w3Fixed_live_le_peak : w3FixedLive ≤ w3FixedPeak :=
  Nat.add_le_add_right w3InitReal_caps_le.2.2.1 65536

private def initCorePrefixCum : Nat :=
  5 * r1bStepBoundedCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum

private def eInitD3Cum : Nat := initCorePrefixCum + w3FixedCum
private def eInitD3Live : Nat := 5 * fineReadFileLive sessionCapBytes + w3FixedLive
private def eInitD3Peak : Nat := 5 * fineReadFilePeak sessionCapBytes + w3FixedPeak
private def eInitD3MaxReq : Nat := max (fineReadFileMaxReq sessionCapBytes) w3FixedMaxReq
private def eInitD3GrpS : Nat := 234 * FineScale + w3FixedGrpS

private theorem eInitD3_live_le_peak : eInitD3Live ≤ eInitD3Peak := by
  unfold eInitD3Live eInitD3Peak
  have hlp_rf : fineReadFileLive sessionCapBytes ≤ fineReadFilePeak sessionCapBytes := by decide
  exact Nat.add_le_add (Nat.mul_le_mul_left 5 hlp_rf) w3Fixed_live_le_peak

private theorem eInitD3_phaseCredit {P : PEParams} (g : RunCall) (hi : CliInitD3Inputs P g.i) :
    PhaseCreditSpec fineCostModel (E_initD3 g).initEnv
      eInitD3Cum eInitD3Live eInitD3Peak eInitD3MaxReq := by
  have hdir : (bytesOfString bundleDir).length ≤ 26 := by decide
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := utf8_bundleNames_length_le_16
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hs1 := r1bFileStepBounded_phaseCredit hdir hn1
  have hs2 := r1bFileStepBounded_phaseCredit hdir hn2
  have hs3 := optStage_phaseCredit_init (r1bFileStepBounded_phaseCredit hdir hn3)
  have hs4 := optStage_phaseCredit_init (r1bFileStepBounded_phaseCredit hdir hn4)
  have hs5 := optStage_phaseCredit_init (r1bFileStepBounded_phaseCredit hdir hn5)
  have hss := optStage_phaseCredit_init (splitSigned_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hsi := optStage_phaseCredit_init (splitId_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hds := optStage_phaseCredit_init r1bDeserStage_phaseCredit_init
  have hr1b : PhaseCreditSpec fineCostModel (R1bBinaryBoundedEnv (bytesOfString bundleDir))
      (4 * r1bStepBoundedCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum)
      (4 * fineReadFileLive sessionCapBytes)
      (4 * fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by omega) (by decide) (by decide) (by decide)
  have hw3 : PhaseCreditSpec fineCostModel (W3SlotFixedEnv g)
      w3FixedCum w3FixedLive w3FixedPeak w3FixedMaxReq :=
    (binaryKitW3Fixed_fineSpec g (own_ikp_le_105_of_cliInitD3Inputs hi)).credit
  have hr1c : PhaseCreditSpec fineCostModel (OptStageEnv (R1cEnv (W3SlotFixedEnv g)))
      w3FixedCum w3FixedLive w3FixedPeak w3FixedMaxReq :=
    optStage_phaseCredit_init
      (CliRunArmsPeak.r1c_phaseCredit fineCostModel_modelHyps hw3 w3Fixed_live_le_peak)
  have hlp_rf : fineReadFileLive sessionCapBytes ≤ fineReadFilePeak sessionCapBytes := by decide
  refine (hs1.seq ((optStage_phaseCredit_init hr1b).seq hr1c)).mono ?_ ?_ ?_ ?_
  · unfold eInitD3Cum initCorePrefixCum; omega
  · unfold eInitD3Live; omega
  · unfold eInitD3Peak
    have h4 : 4 * fineReadFileLive sessionCapBytes ≤ 4 * fineReadFilePeak sessionCapBytes :=
      Nat.mul_le_mul_left 4 hlp_rf
    omega
  · unfold eInitD3MaxReq; exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩

private theorem eInitD3_groupSpec {P : PEParams} (g : RunCall) (hi : CliInitD3Inputs P g.i) :
    PhaseGroupSpec fineCostModel (E_initD3 g).initEnv eInitD3GrpS := by
  let dir := bytesOfString bundleDir
  have hs1 := r1bFileStepBounded_groupSpec dir (utf8 "identity-key")
  have hs2 := r1bFileStepBounded_groupSpec dir (utf8 "registration-id")
  have hs3 := optStage_groupSpec_init (r1bFileStepBounded_groupSpec dir (utf8 "signed-pre-key"))
  have hs4 := optStage_groupSpec_init (r1bFileStepBounded_groupSpec dir (utf8 "kyber-pre-key"))
  have hs5 := optStage_groupSpec_init (r1bFileStepBounded_groupSpec dir (utf8 "one-time-pre-key"))
  have hss := optStage_groupSpec_init (splitSigned_groupSpec_init [])
  have hsi := optStage_groupSpec_init (splitId_groupSpec_init [])
  have hds := optStage_groupSpec_init r1bDeserStage_groupSpec_init
  have hr1b : PhaseGroupSpec fineCostModel (R1bBinaryBoundedEnv dir) (192 * FineScale) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by generalize FineScale = fs; omega)
  have hw3 : PhaseGroupSpec fineCostModel (W3SlotFixedEnv g) w3FixedGrpS :=
    (binaryKitW3Fixed_fineSpec g (own_ikp_le_105_of_cliInitD3Inputs hi)).groups
  have hr1c : PhaseGroupSpec fineCostModel (OptStageEnv (R1cEnv (W3SlotFixedEnv g))) w3FixedGrpS :=
    optStage_groupSpec_init
      ((hw3.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (by generalize FineScale = fs; omega))
  exact (hs1.seq ((optStage_groupSpec_init hr1b).seq hr1c)).mono
    (by unfold eInitD3GrpS; generalize FineScale = fs; omega)

private def initArmWideCum : Nat :=
  max (initArmDeltaCum (pathDeltaCum 26 16) sessionCapBytes eInitD3Cum)
    (initCorePrefixCum + eInitD3Cum)

private def initArmWideLive : Nat :=
  max (initArmDeltaLive (pathDeltaLive 26 16) eInitD3Live)
    (5 * fineReadFileLive sessionCapBytes + eInitD3Live)

private def initArmWidePeak : Nat :=
  max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) sessionCapBytes eInitD3Peak)
    (5 * fineReadFilePeak sessionCapBytes + eInitD3Peak)

private def initArmWideMaxReq : Nat :=
  max (initArmMaxReq (pathMaxReq 26 16) sessionCapBytes eInitD3MaxReq)
    (max (fineReadFileMaxReq sessionCapBytes) eInitD3MaxReq)

private theorem initArmWide_live_le_peak : initArmWideLive ≤ initArmWidePeak := by
  unfold initArmWideLive initArmWidePeak initArmDeltaLive initArmDeltaPeak eInitD3Live eInitD3Peak
    w3FixedLive w3FixedPeak
  have hlp := w3InitReal_caps_le.2.2.1
  have hrf : fineReadFileLive sessionCapBytes ≤ fineReadFilePeak sessionCapBytes := by decide
  have hpd : pathDeltaLive 26 16 ≤ pathDeltaPeak 26 16 := by decide
  omega

private theorem initArmBinaryEnv_eInitD3_phaseCredit {P : PEParams} (g : RunCall)
    (hi : CliInitD3Inputs P g.i) :
    PhaseCreditSpec fineCostModel
      (InitArmBinaryEnv cliIo.rd (runFiles g.i) (bytesOfString bundleDir) (E_initD3 g).initEnv)
      initArmWideCum initArmWideLive initArmWidePeak initArmWideMaxReq := by
  let dir := bytesOfString bundleDir
  have hdir : dir.length ≤ 26 := by decide
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := utf8_bundleNames_length_le_16
  have hinit := eInitD3_phaseCredit g hi
  have hop := CliRunArmsPeak.initArm_phaseCredit_of_paths fineCostModel_modelHyps
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn1)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn2)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn3)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn4)
    (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps hdir hn5)
    (fun _ bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles g.i) _ bs hrd)
    hinit eInitD3_live_le_peak
  have hsm14 : 14 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hs1 := r1bFileStepPlain_phaseCredit (files := runFiles g.i) hdir hn1
  have hs2 := r1bFileStepPlain_phaseCredit (files := runFiles g.i) hdir hn2
  have hs3 := optStage_phaseCredit_init (r1bFileStepPlain_phaseCredit (files := runFiles g.i) hdir hn3)
  have hs4 := optStage_phaseCredit_init (r1bFileStepPlain_phaseCredit (files := runFiles g.i) hdir hn4)
  have hs5 := optStage_phaseCredit_init (r1bFileStepPlain_phaseCredit (files := runFiles g.i) hdir hn5)
  have hss := optStage_phaseCredit_init (splitSigned_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hsi := optStage_phaseCredit_init (splitId_small_phaseCredit fineCostModel_modelHyps hsm14 [])
  have hds := optStage_phaseCredit_init r1bDeserStage_phaseCredit_init
  have hr1b : PhaseCreditSpec fineCostModel (R1bBinaryEnv cliIo.rd (runFiles g.i) dir)
      (4 * r1bStepBoundedCum + 2 * splitSignedDeltaCum + splitIdDeltaCum + r1bDeserStageCum)
      (4 * fineReadFileLive sessionCapBytes)
      (4 * fineReadFilePeak sessionCapBytes)
      (fineReadFileMaxReq sessionCapBytes) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by omega) (by decide) (by decide) (by decide)
  have hr1c : PhaseCreditSpec fineCostModel (OptStageEnv (R1cEnv (E_initD3 g).initEnv))
      eInitD3Cum eInitD3Live eInitD3Peak eInitD3MaxReq :=
    optStage_phaseCredit_init
      (CliRunArmsPeak.r1c_phaseCredit fineCostModel_modelHyps hinit eInitD3_live_le_peak)
  have hlp_rf : fineReadFileLive sessionCapBytes ≤ fineReadFilePeak sessionCapBytes := by decide
  have hcore : PhaseCreditSpec fineCostModel
      (InitArmBinaryCoreEnv cliIo.rd (runFiles g.i) dir (E_initD3 g).initEnv)
      (initCorePrefixCum + eInitD3Cum)
      (5 * fineReadFileLive sessionCapBytes + eInitD3Live)
      (5 * fineReadFilePeak sessionCapBytes + eInitD3Peak)
      (max (fineReadFileMaxReq sessionCapBytes) eInitD3MaxReq) := by
    refine (hs1.seq ((optStage_phaseCredit_init hr1b).seq hr1c)).mono ?_ ?_ ?_ ?_
    · unfold initCorePrefixCum; omega
    · omega
    · have h4 : 4 * fineReadFileLive sessionCapBytes ≤ 4 * fineReadFilePeak sessionCapBytes :=
        Nat.mul_le_mul_left 4 hlp_rf
      omega
    · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
  exact hop.or hcore

private theorem initArmBinaryEnv_eInitD3_groupSpec {P : PEParams} (g : RunCall)
    (hi : CliInitD3Inputs P g.i) :
    PhaseGroupSpec fineCostModel
      (InitArmBinaryEnv cliIo.rd (runFiles g.i) (bytesOfString bundleDir) (E_initD3 g).initEnv)
      (234 * FineScale + eInitD3GrpS) := by
  let dir := bytesOfString bundleDir
  let files := runFiles g.i
  have hinit := eInitD3_groupSpec g hi
  have hop : PhaseGroupSpec fineCostModel (InitArmEnv cliIo.rd files dir (E_initD3 g).initEnv)
      (234 * FineScale + eInitD3GrpS) :=
    (initArmEnv_fine_groupSpec cliIo.rd files dir hinit).mono (by generalize FineScale = fs; omega)
  have hs1 := r1bFileStepPlain_groupSpec files dir (utf8 "identity-key")
  have hs2 := r1bFileStepPlain_groupSpec files dir (utf8 "registration-id")
  have hs3 := optStage_groupSpec_init (r1bFileStepPlain_groupSpec files dir (utf8 "signed-pre-key"))
  have hs4 := optStage_groupSpec_init (r1bFileStepPlain_groupSpec files dir (utf8 "kyber-pre-key"))
  have hs5 := optStage_groupSpec_init (r1bFileStepPlain_groupSpec files dir (utf8 "one-time-pre-key"))
  have hss := optStage_groupSpec_init (splitSigned_groupSpec_init [])
  have hsi := optStage_groupSpec_init (splitId_groupSpec_init [])
  have hds := optStage_groupSpec_init r1bDeserStage_groupSpec_init
  have hr1b : PhaseGroupSpec fineCostModel (R1bBinaryEnv cliIo.rd files dir) (192 * FineScale) :=
    (hs2.seq (hs3.seq (hss.seq (hs4.seq (hss.seq (hs5.seq (hsi.seq hds))))))).mono
      (by generalize FineScale = fs; omega)
  have hr1c : PhaseGroupSpec fineCostModel (OptStageEnv (R1cEnv (E_initD3 g).initEnv)) eInitD3GrpS :=
    optStage_groupSpec_init
      ((hinit.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (by generalize FineScale = fs; omega))
  have hcore : PhaseGroupSpec fineCostModel
      (InitArmBinaryCoreEnv cliIo.rd files dir (E_initD3 g).initEnv)
      (234 * FineScale + eInitD3GrpS) :=
    (hs1.seq ((optStage_groupSpec_init hr1b).seq hr1c)).mono (by generalize FineScale = fs; omega)
  exact (hop.or hcore).mono (max_self_le_init _)

private def r0InitSessCum : Nat :=
  max r0Opened1MiBCum (21185 + max 738 (fineReadFileCum sessionCapBytes) + addressTryParseDeltaCum)

private def r0InitSessLive : Nat :=
  max r0Opened1MiBLive (fineReadFileLive sessionCapBytes + addressTryParseDeltaLive)

private def r0InitSessPeak : Nat :=
  max r0Opened1MiBPeak
    (max (fineReadFilePeak sessionCapBytes)
      (fineReadFileLive sessionCapBytes + addressTryParseDeltaPeak))

private def r0InitSessMaxReq : Nat :=
  max r0Opened1MiBMaxReq (max (max 256 (fineReadFileMaxReq sessionCapBytes)) addressTryParseMaxReq)

private theorem r0BinaryEnv_initSess_phaseCredit (g : RunCall) :
    PhaseCreditSpec fineCostModel (R0BinaryEnv cliIo.rd g)
      r0InitSessCum r0InitSessLive r0InitSessPeak r0InitSessMaxReq := by
  have hcapSess : ∀ bs,
      cliIo.rd (runFiles g.i) (pathOf StoresGhost.opened.identity.own.path (utf8 "address")) =
        .ok bs → bs.length ≤ sessionCapBytes :=
    fun bs hrd => cliIo_rd_ok_length_le_sessionCapBytes (runFiles g.i) _ bs hrd
  have hop : PhaseCreditSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i))
      r0Opened1MiBCum r0Opened1MiBLive r0Opened1MiBPeak r0Opened1MiBMaxReq :=
    CliRunArmsPeak.r0Opened_phaseCredit_of_path fineCostModel_modelHyps
      (DirPeakSpec.path_phaseCredit fineCostModel_modelHyps
        (by decide : StoresGhost.opened.identity.own.path.length ≤ 26) utf8_address_length_le)
      hcapSess
  have hown64 : DirDomainCaps 64 0 0 StoresGhost.opened.identity.own :=
    dirDomainCaps_opened_own.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)
  have hdg := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address") hown64
    (Nat.le_trans utf8_address_length_le (by decide)) hcapSess
  have hmax_eq : max 0 sessionCapBytes = sessionCapBytes := Nat.zero_max sessionCapBytes
  rw [hmax_eq] at hdg
  have hafter : PhaseCreditSpec fineCostModel (PreAfterGetEnv g)
      addressTryParseDeltaCum addressTryParseDeltaLive
      addressTryParseDeltaPeak addressTryParseMaxReq := by
    unfold PreAfterGetEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok ownB =>
      exact phaseCredit_seq_freeOnly_right fineCostModel_modelHyps
        (addressTryParse_phaseCredit fineCostModel_modelHyps ownB) (fun _ hf => hf) (Nat.le_refl _)
  exact hop.or (hdg.seq hafter)

private theorem r0BinaryEnv_initSess_groupSpec (g : RunCall) :
    PhaseGroupSpec fineCostModel (R0BinaryEnv cliIo.rd g) (42 * FineScale) := by
  have hop : PhaseGroupSpec fineCostModel (R0OpenedEnv cliIo.rd (runFiles g.i)) (42 * FineScale) :=
    (r0OpenedEnv_fine_groupSpec cliIo.rd (runFiles g.i)).mono (by unfold FineScale; decide)
  have hdg := dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd (runFiles g.i)
    StoresGhost.opened.identity.own (utf8 "address")
  have hafter : PhaseGroupSpec fineCostModel (PreAfterGetEnv g) (3 * FineScale) := by
    unfold PreAfterGetEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
    | error _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | ok ownB =>
      have haddr : PhaseGroupSpec fineCostModel (· = addressEvents uuidTryParse ownB)
          (3 * FineScale) := by
        unfold addressEvents
        cases addrParse uuidTryParse ownB with
        | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | some a => exact PhaseGroupSpec.rustAlloc_any fineCostModel a.name.length 1
      exact (haddr.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
        (by generalize FineScale = fs; omega)
  exact (hop.or ((hdg.seq hafter).mono (by generalize FineScale = fs; omega))).mono
    (max_self_le_init _)

private def initD3RunCum : Nat := r0InitSessCum + initArmWideCum
private def initD3RunLive : Nat := r0InitSessLive + initArmWideLive
private def initD3RunPeak : Nat := max r0InitSessPeak (r0InitSessLive + initArmWidePeak)
private def initD3RunMaxReq : Nat := max r0InitSessMaxReq initArmWideMaxReq
private def initD3RunGrpS : Nat :=
  cliRunOpenedCustomPksmGrpS msgCapBytes (pksmCanonSliceGrpS msgCapBytes) eInitD3GrpS 0 0 0 +
    27 * FineScale

private def initD3MainCum : Nat :=
  123250 + m3PhaseDeltaCum_tight + initD3RunCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

private def initD3MainLive : Nat := cliMainTightLiveOf initD3RunLive
private def initD3MainPeak : Nat := cliMainTightPeakOf initD3RunLive initD3RunPeak
private def initD3MainReq : Nat := cliMainTightReqOf initD3RunMaxReq
private def initD3MainGrpS : Nat :=
  cliMainWidenedSetupFineGrpS + initD3RunGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

private theorem initD3Main_arith_bounds :
    initD3MainLive ≤ initD3MainPeak ∧
    cliDecoupledRamNeed cliDefaultStaticBytes initD3MainCum initD3MainPeak initD3MainReq
      ((initD3MainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount initD3MainCum initD3MainPeak
      initD3MainReq ((initD3MainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
  ⟨by unfold initD3MainLive initD3MainPeak cliMainTightLiveOf cliMainTightPeakOf
        cliMainDeltaLive_tight cliMainDeltaPeak_tight
      exact Nat.le_trans (Nat.add_le_add_left
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _) (Nat.le_max_right _ _),
   by decide,
   by decide⟩

private theorem realCliMainBinaryEnvOf_eInitD3_fitsEnv {P : PEParams}
    (i : Inputs) (hi : CliInitD3Inputs P i) :
    FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E_initD3 i) := by
  obtain ⟨st, files, t, hwf, hs, hb, heq⟩ := hi
  have hargv_eq : i.argv = ["init", (partyAddress st.party.other).text, bundleDir] := heq.1
  have hargv_le : i.argv.length ≤ 3 := by rw [hargv_eq]; exact Nat.le_refl 3
  have hsm1024 : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (initD3RunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      initD3RunLive
      (max initD3RunPeak
        (initD3RunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max initD3RunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hparse_init : parseArgs uuidTryParse
        ([bytesOfString "init", bytesOfString (partyAddress st.party.other).text,
          bytesOfString bundleDir]) = some w.g.c := by
      simpa only [w.g_i, hargv_eq, List.map_cons, List.map_nil] using w.parse_ok
    obtain ⟨peerV, hc⟩ := parseArgs_init_bundleDir_init hparse_init
    have hi_wg : CliInitD3Inputs P w.g.i := w.g_i.symm ▸ ⟨st, files, t, hwf, hs, hb, heq⟩
    have harm : PhaseCreditSpec fineCostModel
        (RunArmBinaryEnv cliIo.rd (runFiles w.g.i) (E_initD3 w.g) sessionCapBytes w.g.i.stdin w.g.c)
        initArmWideCum initArmWideLive initArmWidePeak initArmWideMaxReq := by
      rw [hc]
      exact initArmBinaryEnv_eInitD3_phaseCredit w.g hi_wg
    have haj := phaseCredit_seq_freeOnly_right fineCostModel_modelHyps harm (fun _ hf => hf)
      initArmWide_live_le_peak
    have hrun : PhaseCreditSpec fineCostModel
        (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
        initD3RunCum initD3RunLive initD3RunPeak initD3RunMaxReq :=
      phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf)
        ((r0BinaryEnv_initSess_phaseCredit w.g).seq haj)
    refine (hrun.seq ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
      (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact max_mono_init (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact max_mono_init (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (initD3RunCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) + m6DeltaCum)
      initD3RunLive
      (max initD3RunPeak
        (initD3RunLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max initD3RunMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel (RealCliMainBinaryEnvOf E_initD3 i)
      initD3MainCum initD3MainLive initD3MainPeak initD3MainReq := by
    refine ((cliMainBoundedSetup_phaseCredit_fine hargv_le).seq
      (optStage_phaseCredit_init hex)).mono ?_ ?_ ?_ ?_
    · unfold initD3MainCum; simp only [Nat.add_assoc]; exact Nat.le_refl _
    · unfold initD3MainLive cliMainTightLiveOf cliMainDeltaLive_tight; exact Nat.le_refl _
    · unfold initD3MainPeak cliMainTightPeakOf cliMainDeltaPeak_tight; exact Nat.le_refl _
    · unfold initD3MainReq cliMainTightReqOf cliMainMaxReq
      have h16k : max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes; decide
      rw [h16k]
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (initD3RunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hparse_init : parseArgs uuidTryParse
            ([bytesOfString "init", bytesOfString (partyAddress st.party.other).text,
              bytesOfString bundleDir]) = some w.g.c := by
          simpa only [w.g_i, hargv_eq, List.map_cons, List.map_nil] using w.parse_ok
        obtain ⟨peerV, hc⟩ := parseArgs_init_bundleDir_init hparse_init
        have hi_wg : CliInitD3Inputs P w.g.i := w.g_i.symm ▸ ⟨st, files, t, hwf, hs, hb, heq⟩
        have harm_g : PhaseGroupSpec fineCostModel
            (RunArmBinaryEnv cliIo.rd (runFiles w.g.i) (E_initD3 w.g)
              sessionCapBytes w.g.i.stdin w.g.c)
            (234 * FineScale + eInitD3GrpS) := by
          rw [hc]
          exact initArmBinaryEnv_eInitD3_groupSpec w.g hi_wg
        have hrun : PhaseGroupSpec fineCostModel
            (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
            initD3RunGrpS :=
          (cliRunOfR0_fine_groupSpec (r0BinaryEnv_initSess_groupSpec w.g) harm_g).mono
            (by unfold initD3RunGrpS; decide)
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv (CliRunBinaryEnv cliIo.rd (E_initD3 w.g) sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            (initD3RunGrpS + cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel (RealCliMainBinaryEnvOf E_initD3 i) initD3MainGrpS :=
    ((cliMainBoundedSetup_fine_groupSpec hargv_le).seq (optStage_groupSpec_init hex_grp)).mono
      (by unfold initD3MainGrpS; generalize FineScale = fs; omega)
  obtain ⟨hlp, hram, hva⟩ := initD3Main_arith_bounds
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) rfl hram hva

end InitD3Priv

section
set_option linter.unusedVariables false

/-- Concrete `MainEntryBudgetFitsCapOf` at `cliBudgetLimits` (`1 GiB`) for `initD3ScopedRun`
(`CliInitD3Inputs ⟨W.C, W.Q⟩`, covering `initOverFileCap` with `ReadFileRuleEnvFixed cliIo.rd`). -/
theorem mainEntryBudgetFitsCapOf_initD3ScopedRun_fixed [LibsignalPlacement]
    {M : AllocCostModel}
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget M) (B : RunBudgets)
    (DecPkSlotEnv : DecPkGhost → List AllocEvent → Prop)
    (hNwDom : ∀ (i : Inputs) (nw : List (String × List (BitVec 8))) (out : List (BitVec 8)),
      CliInitD3Inputs ⟨W.C, W.Q⟩ i →
      runAns S i = some (some (nw, out)) →
      nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsFixed W A B
            (realCliInitBinarySlotEnvFixed W) DecPkSlotEnv)
          PksmTryFromEnv S))
      (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) := by
  exact mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    realCliMainBinaryEnvOf_eInitD3_fitsEnv
    (fun i _ ⟨_, _, _, _, _, _, heq⟩ _ _ => by rw [heq.2.2.1]; exact Nat.zero_le _)
    hNwDom
    (fun g hi hparse _ _ => runEnvFixed_sub_cliRunBinaryEnv_initD3 S W A B DecPkSlotEnv g hi hparse)

end

end LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
