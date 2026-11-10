/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# D3 `pathB` Top-Join Assembler at `h2k_ghFixedK` (`ElfSlicesPqOomH2KD3JoinPathB`)

**Checked by Lean.**

Defines the unguarded and `PeerSpqrStateTight640`-guarded Slot-`520` (`decryptPrekey`) pre-only
`FdsGe3Closed` interfaces for D3 `pathB`, proves the guarded-of-unguarded Slot-`520` adapter
(`h2kd3_slotOk_preFd_guarded_of_unguarded`) and `MainEntryBudgetFitsCapOf` for `cliRunSemPathB X W`,
and lifts Block `579` to Block `617` to close `h2asm_GhostMainOkPathBK mpl mmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinPathB

open Arm64 ProofLib SepProp
open Arm64.Obj (Image MultiPlacement)
open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib stdinCapBytes)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRunBudgets cliRunBudgets_placed cliRunNeeds inputOf instLsCodeInvFrozen
   parseArgs)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost RunNeeds addrValOf mkSlot runFiles runRel slotOut slotTrace)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliPollSessKitPlaced loadRec_scopeKit_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots
  (FilesOkPeer encodeInjOn_deserializeScopeP_Q loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliDpPollTrustedWideBridge (not_fitsEnv_top)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (d3SlotMainFitsOneGiBOf)
open LibsignalBinary.Proofs.PeakBudget.D3MatchingPathBSeqFreeR
  (DecPkD3MatchingPathBGvEnv DecPkD3MatchingPathBGvSeqFreeOfReadEnv MatchingPathBGvMainEnv
   MatchingPathBGvPollEnv decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0')
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (recv_rest_length_le_msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (CliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf (TryDecryptCliLinkedEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryCallSiteDomCmk0 W4BinaryRecvPrekeyDomCmk0
   W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   realCliDecPkBinaryWideSlotEnvCmkDom0Fixed'
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'
   realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_ghost_congr
   w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec'
   w4CmkDom0Cum w4CmkDom0GrpS109 w4CmkDom0GrpSOf_109_eq w4CmkDom0Live w4CmkDom0MaxReq
   w4CmkDom0Peak w4CmkDom0_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SignalSession.Cli.D3
  (DecPkOkPathB pathB_scopeIn_and_match_of_decPkOkPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverEnvPlacedBudget
  (peerSpqrStateTight640_of_cliPqOrD3Recv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
  (h9r2_fitsCap_pathB_of_dom0_singleSlot h9r2_honestD3RunSlotEnvs h9r2_initEnv_r1c_congr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (cliRunArmEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigFrozenPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageP2DefsPlacedBudget
  (StageP3Env StageP3ErrEnv StageP3OkPrefixEnv stageP3TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_GhostMainOkPathBK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (h2kb_hole2_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
  (h2kd3_SpineBD3SlotsRunTightK h2kd3_decSigFrozenSlotWithPreFd_congr
   h2kd3_encSlotWithPreFd_congr h2kd3_runProofs_encDef_eq_agree h2kd3_witnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
  (ghostMainSubroutineD3_of_domScopedRunTight_preFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (extract_withPreFdsGe3Closed h2ki_RunTightAt579PreFd h2ki_W1EncryptSlot464OkK
   h2ki_W2DecryptSignalSlot463OkK h2ki_W3InitSlot521OkK slotWithPreFdsGe3Closed
   withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA (h2k_hole2_hioOfFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2
   fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2
   fits2_w2DecSigExact_groupSpec fits2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hMainStk hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open VerifiedLibraries (mallocngLib)

/-! ## `PathB` `RunSlotEnvs` and Slot-`520` Interfaces -/

/-- D3 `RunSlotEnvs` bundle for `pathB` at `realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'`. -/
noncomputable abbrev h2kd3_pathBSlotEnvs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    RunSlotEnvs :=
  h9r2_honestD3RunSlotEnvs
    (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    W A cliRunBudgets (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `pathB` unguarded) pre-only
`FdsGe3Closed` interface at `DecPkD3MatchingPathBGvSeqFreeOfReadEnv … (w4s2_TryDecryptTopStateGuardedEnv W)`. -/
def h2kd3_W4PathBSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2kd3_pathBSlotEnvs A X W
    let DecPkEnv₀ := DecPkD3MatchingPathBGvSeqFreeOfReadEnv A.repAlloc W cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W)
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits { sEnvs with decryptPrekey := DecPkEnv₀ }
        (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2kd3_W4PathBSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2kd3_W4PathBSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `pathB` guarded) pre-only `FdsGe3Closed`
interface at `realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'`. -/
def h2kd3_W4PathBGuardedSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2kd3_pathBSlotEnvs A X W
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2kd3_W4PathBGuardedSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2kd3_W4PathBGuardedSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-! ## `TopStateTight` Collapse and Guarded-of-Unguarded Adapter -/

private theorem h2kd3_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs :=
  h.elim (fun ha => Or.inl (h1 evs ha))
    (fun ⟨e1, e2, heq, ha, hb⟩ => Or.inr ⟨e1, e2, heq, h1 e1 ha, h2 e2 hb⟩)

/-- Collapses `w4s2_TryDecryptTopStateGuardedEnv W` to `TryDecryptCliLinkedEnvOf 109 W.C W.Q.K`
under `PeerSpqrStateTight640` and lifts `DecPkD3MatchingPathBGvSeqFreeOfReadEnv` into
`realCliDecPkBinaryWideSlotEnvCmkDom0Fixed'`. -/
theorem h2kd3_gvSeqFree_sub_cmkDom0' [LibsignalPlacement]
    (A : RustAlloc) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : DecPkGhost} {evs : List AllocEvent}
    (hfPeer : FilesOkPeer scopeIn g.F g.peer.val)
    (hdecOk : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn g.F g.peer.val g.me.val g.msg)
    (hTight : PeerSpqrStateTight640 W.C.F W.Q.K g.F g.peer.val)
    (hevs : DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) (w4s2_TryDecryptTopStateGuardedEnv W) g evs) :
    realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W g evs := by
  have hevs109 :
      DecPkD3MatchingPathBGvSeqFreeOfReadEnv A W cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) (TryDecryptCliLinkedEnvOf 109 W.C W.Q.K) g evs := by
    unfold DecPkD3MatchingPathBGvSeqFreeOfReadEnv DecPkD3MatchingPathBGvEnv
      MatchingPathBGvPollEnv at hevs ⊢
    dsimp only at hevs ⊢
    split at hevs
    · next htr =>
      simp only [htr, ↓reduceIte]
      exact hevs
    · next htr =>
      simp only [htr, ↓reduceIte]
      refine h2kd3_seqEnv_mono (fun _ h => h) ?_ hevs
      rintro evs234 ⟨r, sess, hload_rel, hcur, hmain⟩
      have hload_rel' := hload_rel
      dsimp only [cliPollSessKitPlaced] at hload_rel'
      obtain ⟨hloadS, _, _, _, _, _, _⟩ :=
        pathB_scopeIn_and_match_of_decPkOkPathB encodeInjOn_deserializeScopeP_Q (fun _ h => h)
          hfPeer hdecOk hload_rel' hcur
      have hloadK : loadRec scopeKit g.F g.peer.val = .ok (some ⟨some sess⟩) :=
        (loadRec_scopeKit_eq encodeInjOn_deserializeScopeP_Q (fun _ h => h) hfPeer).trans hloadS
      have hTop : TopStateTight W.C.F W.Q.K sess.state.pqRatchetState := by
        unfold PeerSpqrStateTight640 at hTight
        rw [hloadK] at hTight
        exact hTight sess rfl
      refine ⟨r, sess, hload_rel, hcur, ?_⟩
      unfold MatchingPathBGvMainEnv at hmain ⊢
      rcases hmain with hP2 | ⟨hrem, recG, hex, hgv, hseq⟩
      · exact Or.inl hP2
      · refine Or.inr ⟨hrem, recG, hex, hgv, h2kd3_seqEnv_mono (fun _ h => h) ?_ hseq⟩
        rintro evs34 (hP3 | ⟨hver, G₁, G', pt, hcl, haft, hmod, hok⟩)
        · refine Or.inl ?_
          unfold StageP3Env at hP3 ⊢
          split at hP3
          · next hv =>
            simp only [hv, ↓reduceIte]
            rcases hP3 with ⟨G₁, hcl, herr⟩
            refine ⟨G₁, hcl, ?_⟩
            unfold StageP3ErrEnv at herr ⊢
            rw [← w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
              (stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins)
              hTop]
            exact herr
          · next hv =>
            simp only [hv, ↓reduceIte]
            exact hP3
        · refine Or.inr ⟨hver, G₁, G', pt, hcl, haft, hmod, h2kd3_seqEnv_mono ?_ (fun _ h => h) hok⟩
          intro evsP3 hpfx
          unfold StageP3OkPrefixEnv at hpfx ⊢
          rw [← w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W
            (stageP3TryDecryptEnvArgs G₁ sess.state g.peer g.me g.msgG.msg g.msg.message g.coins)
            hTop]
          exact hpfx
  exact decPkD3MatchingPathBGvSeqFreeOfReadEnv_sub_cmkDom0' A X W cliRunBudgets_placed
    (fun _ _ h => h) hfPeer hdecOk hTight hevs109

/-- Lifts an unguarded `DecPkEnv₀` Slot-`520` `slotWithPreFdsGe3Closed` `.OkPlaced` contract to
`realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W`, ruling out `¬ PeerSpqrStateTight640` via
`not_fitsEnv_top`. -/
theorem h2kd3_slotOk_preFd_guarded_of_unguarded [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {DecPkEnv₀ : DecPkGhost → List AllocEvent → Prop}
    {sEnvs : RunSlotEnvs} {needs : RunNeeds}
    (hsEnv : sEnvs.decryptPrekey = realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)
    (hUnguarded :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A lim { sEnvs with decryptPrekey := DecPkEnv₀ }
          (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced prog entry)
    (hBridge : ∀ x evs,
      FilesOkPeer scopeIn x.F x.peer.val →
      DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg →
      PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
      DecPkEnv₀ x evs →
      realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' X W x evs) :
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A lim sEnvs (cliRunSemPathB X W) needs).decryptPrekey).OkPlaced
      prog entry := by
  intro stk hstk1 hstk2
  have hSub0 := hUnguarded stk hstk1 hstk2
  dsimp only [slotWithPreFdsGe3Closed, slotsOfSigPkFrozenPlaced, mkSlot] at hSub0 ⊢
  rw [hsEnv]
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre0 hsp _ => ?_
  obtain ⟨hfds, hpre⟩ := extract_withPreFdsGe3Closed hpre0
  dsimp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit⟩,
    hrest⟩ := hpre
  by_cases hTight : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val
  · have hdOk' : DecPkOkPathB ⟨W.C, W.Q⟩ scopeIn x.F x.peer.val x.me.val x.msg :=
      ⟨hdOk.party, hdOk.loadedMatch, hdOk.keyPairLt, hdOk.preKeysWf, hdOk.baseKeysLt⟩
    have hImp : ∀ evs, DecPkEnv₀ x evs →
        realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs :=
      fun evs hevs0 _ => hBridge x evs hfOk.1 hdOk' hTight hevs0
    have hfit0 : FitsEnv M lim st (DecPkEnv₀ x) :=
      fun evs hevs0 => hfit evs (hImp evs hevs0)
    have hpre1 :
        s0.mem ⊨
          (withPreFdsGe3Closed
            (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced
              A lim DecPkEnv₀ (cliRunSemPathB X W) stk)).pre (x, st) s0 ∗ R := by
      dsimp only [withPreFdsGe3Closed]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hfds, ?_⟩
      dsimp only [
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced]
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hF0, hfOk, hdOk, hsp_le, hfit0⟩,
        hrest⟩
    refine hSub0.mono_outcome (x, st) R s0 hpc hrun hpre1 hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | hp | hex | ho
    · refine Or.inl ⟨hret, hcc, ProofLib.Satisfies.mono (sepConj_mono_left ?_) hpost⟩
      dsimp only [withPreFdsGe3Closed,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecFrozenPlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlacedOf,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecBasePlaced,
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget.decPkSlotSpecPlaced,
        withLsCodeRoLoaded]
      refine Entails.sepExists_elim fun evs => Entails.sepExists_right evs ?_
      refine Entails.sepExists_elim fun g' => Entails.sepExists_right g' ?_
      refine Entails.sepExists_elim fun e => Entails.sepExists_right e ?_
      refine Entails.pure_left fun ⟨hevs0, htr, hout_e⟩ => ?_
      have hPure :
          (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W x evs ∧ slotTrace s0 sf ∧
            slotOut ((cliRunSemPathB X W).decryptPrekey x.F x.peer.val x.me.val x.msg x.coins)
              g' e s0 sf) = True :=
        propext ⟨fun _ => trivial, fun _ => ⟨hImp evs hevs0, htr, hout_e⟩⟩
      rw [hPure, pure_true, emp_sepConj]
      exact Entails.refl _
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hex))
    · exact Or.inr (Or.inr (Or.inr ho))
  · exfalso
    refine not_fitsEnv_top M lim st (fun evs _ => ?_)
    exact hfit evs (fun h => False.elim (hTight h))

/-! ## `Dom0` `SingleSlotFineSpec` and `MainEntryBudgetFitsCapOf` for `PathB` -/

/-- `PathB` `RunEnv` family at `[LibsignalPlacement]`, matching `H9PathBAssemblyHonestR2`. -/
noncomputable abbrev h2kd3_pathBRunEnvAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (h2kd3_pathBSlotEnvs
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) X W)
      PksmTryFromEnv (cliRunSemPathB X W))

/-- `Dom0` `SingleSlotFineSpec` witness at `realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed'`. -/
def h2kd3_decPkDom0_singleSlot [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (meV peerV : AddrV) (rest : List (BitVec 8)) (pm : PreKeySignalMessage)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hin : (inputOf g.i g.c).length ≤ stdinCapBytes)
    (hc : g.c = .recv peerV)
    (hst : g.i.stdin = 3#8 :: rest)
    (hpk : (cliRunSemPathB X W).pksmParse rest = some pm) :
    SingleSlotFineSpec
      (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W (r3bDecPkGhost g meV peerV pm)) :=
  let hi_dom : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ g.i :=
    hi_g.elim Or.inl Or.inr
  let S4 := w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec' (P := ⟨W.C, W.Q⟩) (c := .recv peerV)
    (i := g.i) hi_dom
  have hSub : ∀ evs,
      realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W (r3bDecPkGhost g meV peerV pm) evs →
      ∃ w : W4BinaryRecvPrekeyParamsCmk,
        W4BinaryRecvPrekeyDomCmk0
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
          (.recv peerV) g.i w ∧
        W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs := by
    intro evs hevs
    have hp640 : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) (addrValOf peerV) :=
      peerSpqrStateTight640_of_cliPqOrD3Recv hi_dom hp
    have hpk' : pksmParse rest = some pm := hpk
    have hct_cap : pm.message.ciphertext.length ≤ msgCapBytes :=
      Nat.le_trans (pksmParse_lengths_le hpk').2.2.1
        (recv_rest_length_le_msgCapBytes hin hc hst)
    obtain ⟨w4, hcs0, _hik, _hbk, henv⟩ := hevs hp640
    have hdom0 :=
      W4BinaryCallSiteDomCmk0.toCmkDom0Of
        w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps hcs0 hp hct_cap
    have hdom4 :
        W4BinaryRecvPrekeyDomCmk0
          w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
          (.recv peerV) g.i w4 := by
      intro pAddr hpAddr
      injection hpAddr with hpEq
      subst hpEq
      exact ⟨hcs0.1.eq_peerVal, hdom0.1.outer_dom.peer_len, hcs0.1.eq_files, hcs0.1.eq_rd, hdom0⟩
    exact ⟨w4, hdom4, henv⟩
  { cum := w4CmkDom0Cum
    live := w4CmkDom0Live
    peak := w4CmkDom0Peak
    maxReq := w4CmkDom0MaxReq
    grpS := w4CmkDom0GrpS109
    credit := PhaseCreditSpec.of_imp hSub S4.credit
    live_le_peak := w4CmkDom0_live_le_peak
    groups := PhaseGroupSpec.of_imp (w4CmkDom0GrpSOf_109_eq ▸ S4.groups) hSub }

/-- `MainEntryBudgetFitsCapOf` for D3 `pathB` (`cliRunSemPathB X W` + `h2kd3_pathBSlotEnvs`),
closed via `H9PathBAssemblyHonestR2.h9r2_fitsCap_pathB_of_dom0_singleSlot`. -/
theorem h2kd3_fitsCap_pathB [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_pathBSlotEnvs A X W)
          PksmTryFromEnv (cliRunSemPathB X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) := by
  have h :
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv
          (cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            (h2kd3_pathBSlotEnvs A X W)
            PksmTryFromEnv (cliRunSemPathB X W)))
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) :=
    h9r2_fitsCap_pathB_of_dom0_singleSlot
      (fun {_M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
      (fun {_M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
      img X W A cliRunBudgets
      (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' X W)
      w4CmkDom0Cum w4CmkDom0Live w4CmkDom0Peak w4CmkDom0MaxReq w4CmkDom0GrpS109
      (fun g peerV M' A' w1R hi hp hc hrep hdom => by
        have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
            ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
          congrArg
            (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) =>
              f A' w1R.B)
            (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
        rw [heq]
        exact ckx2_w1EncExact_phaseCredit W g peerV M' A' w1R hi hp hc hrep hdom)
      (fun g peerV M' A' w1R hi hp hc hrep hdom => by
        have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
            ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
          congrArg
            (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) =>
              f A' w1R.B)
            (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
        rw [heq]
        exact ckx2_w1EncExact_groupSpec W g peerV M' A' w1R hi hp hc hrep hdom)
      (fun g peerV M' A' w2R hi hp hc hrep hdom => by
        have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
            ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
          congrArg
            (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) =>
              f A' w2R.B)
            (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
        rw [heq]
        exact fits2_w2DecSigExact_phaseCredit W g peerV M' A' w2R hi hp hc hrep hdom)
      (fun g peerV M' A' w2R hi hp hc hrep hdom => by
        have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
            ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
          congrArg
            (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) =>
              f A' w2R.B)
            (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
        rw [heq]
        exact fits2_w2DecSigExact_groupSpec W g peerV M' A' w2R hi hp hc hrep hdom)
      (h2kd3_decPkDom0_singleSlot X W)
      (fun _ _ _ _ _ _ _ _ _ _ _ =>
        ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
      w4CmkDom0_live_le_peak
      (by unfold d3SlotMainFitsOneGiBOf; decide)
  have heq :
      cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_pathBSlotEnvs A X W) PksmTryFromEnv (cliRunSemPathB X W) =
        cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_pathBSlotEnvs A X W) PksmTryFromEnv (cliRunSemPathB X W) := rfl
  exact Eq.mp
    (congrArg (fun aEnvs =>
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv aEnvs)
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W)))) heq)
    h

/-! ## Block-`579` to Block-`617` `PathB` Top-Join Assemblers -/

/-- Plugs W1 (`464`), W2 (`463`), W3 (`521`), and guarded `pathB` W4 (`520`) into
`h2kd3_SpineBD3SlotsRunTightK` to discharge Block `579` for `cliRunSemPathB X W`. -/
theorem h2kd3_runTight_pathB_of_guardedIfaces
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK w)
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4Guarded : h2kd3_W4PathBGuardedSlot520OkK w)
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    h2ki_RunTightAt579PreFd w.hblk w.hext_nodup
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (h2kd3_pathBRunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup X W γ tp)
      (cliRunSemPathB X W) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let sEnvs := h2kd3_pathBSlotEnvs A X W
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hEnc :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemPathB X W) needs).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
    dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced, slotsOfPlaced,
      sEnvs, h2kd3_pathBSlotEnvs, h9r2_honestD3RunSlotEnvs]
    exact h2kd3_encSlotWithPreFd_congr rfl rfl rfl
      (h2kd3_runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn).symm
      (hW1 h547 X W γ tp)
  have hDecSig :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemPathB X W) needs).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
    dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced,
      sEnvs, h2kd3_pathBSlotEnvs, h9r2_honestD3RunSlotEnvs]
    exact h2kd3_decSigFrozenSlotWithPreFd_congr rfl rfl
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (hW2 h547 X W γ tp)
  have hInit :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemPathB X W) needs).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521) :=
    hW3 h547 X W γ tp (cliRunSemPathB X W) sEnvs needs rfl rfl rfl rfl rfl
  exact hSpineB h547 (cliRunSemPathB X W) W γ tp sEnvs rfl
    (h9r2_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W A)
    (hole3_decSigEnv_r3a_congr W A)
    (realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_ghost_congr
      w4c_repairedStatesRecvEnvFam X W)
    hEnc hDecSig hInit (hW4Guarded h547 X W γ tp)

/-- Plugs `464`, `463`, `521`, and unguarded `pathB` Slot `520` into
`h2kd3_SpineBD3SlotsRunTightK` via `h2kd3_slotOk_preFd_guarded_of_unguarded` and
`h2kd3_gvSeqFree_sub_cmkDom0'`. -/
theorem h2kd3_runTight_pathB_of_ifaces
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK w)
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4 : h2kd3_W4PathBSlot520OkK w) :
    mpl.base 547 ≠ 0#64 →
    ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      h2ki_RunTightAt579PreFd w.hblk w.hext_nodup
        (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (h2kd3_pathBRunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup X W γ tp)
        (cliRunSemPathB X W) :=
  h2kd3_runTight_pathB_of_guardedIfaces w hSpineB hW1 hW2 hW3
    (fun h547 X W γ tp => by
      letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
      let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
      exact h2kd3_slotOk_preFd_guarded_of_unguarded rfl (hW4 h547 X W γ tp)
        (fun x evs hfPeer hdecOk hTight hevs0 =>
          h2kd3_gvSeqFree_sub_cmkDom0' A.repAlloc X W hfPeer hdecOk hTight hevs0))

/-- Pre-`hTrFrozen` `pathB` Block-`579 → 617` lift at `h2k_ghFixedK mpl mmpl` directly from
post-slot `h2ki_RunTightAt579PreFd`. -/
theorem h2kd3_ghostMainOkPathBK_of_runTight
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hRun :
      mpl.base 547 ≠ 0#64 →
      ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
        h2ki_RunTightAt579PreFd (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
          (letI : LibsignalPlacement :=
            libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
           cliGhostExterns (h2k_ghFixedK mpl mmpl) (cliExternsPlaced mmpl W))
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          (h2kd3_pathBRunEnvAt (mmpl := mmpl)
            (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) X W γ tp)
          (cliRunSemPathB X W)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkPathBK mpl mmpl := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  intro h547 X W
  exact ghostMainSubroutineD3_of_domScopedRunTight_preFd
    (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (h2k_ghFixedK mpl mmpl)
    (@instLsCodeInvFrozen
      (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
    (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) (cliRunSemPathB X W)
    rfl hG (h2k_hole2_hioOfFd mpl mmpl hLs hMm W)
    hole2_hMainStk
    (fun γ tp =>
      @h2kd3_fitsCap_pathB
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
        (default : Image) X W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
    (fun γ tp => hRun h547 X W γ tp)

/-- Guarded-interface variant of `h2kd3_ghostMainOkPathBK_of_ifaces` (taking
`h2kd3_W4PathBGuardedSlot520OkK` directly). -/
theorem h2kd3_ghostMainOkPathBK_of_guardedIfaces
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4Guarded : h2kd3_W4PathBGuardedSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkPathBK mpl mmpl :=
  h2kd3_ghostMainOkPathBK_of_runTight mpl mmpl hLs hMm
    (h2kd3_runTight_pathB_of_guardedIfaces (h2kd3_witnessK mpl mmpl hLs hMm)
      hSpineB hW1 hW2 hW3 hW4Guarded)

/-- Closes `h2asm_GhostMainOkPathBK mpl mmpl` from `h2kd3_SpineBD3SlotsRunTightK`, shared slot
contracts `464` / `463` / `521`, and `h2kd3_W4PathBSlot520OkK`. -/
theorem h2kd3_ghostMainOkPathBK_of_ifaces
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4 : h2kd3_W4PathBSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkPathBK mpl mmpl :=
  h2kd3_ghostMainOkPathBK_of_runTight mpl mmpl hLs hMm
    (h2kd3_runTight_pathB_of_ifaces (h2kd3_witnessK mpl mmpl hLs hMm)
      hSpineB hW1 hW2 hW3 hW4)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinPathB
