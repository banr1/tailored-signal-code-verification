/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CallSiteFacts
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
public import LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut

/-!
# D3 `validMatch` Top-Join Assembler and Shared D3 Spine-B Interface (`ElfSlicesPqOomH2KD3JoinValidMatch`)

**Checked by Lean.**

Defines the shared K-witness handle `h2kd3_witnessK`, the slot-parametric Block-`579` interface
`h2kd3_SpineBD3SlotsRunTight{At,K}` and `encrypt` / `decryptSignal` congruence bridges reused by
`validMatch`, `overD3`, and `pathB`, and the `validMatch` Block-`579 → 617` assemblers closing
`h2asm_GhostMainOkValidMatchK mpl mmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch

open Arm64 (GhostName Program subroutine_ok)
open Arm64.Obj (Image MultiPlacement)
open CryptoGames.LibsignalSessionApi (SessionRecord messageEncrypt)
open CryptoVerification
  (LibsignalFrozen LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel wirePrekey)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApiRepr (serializeAddrVals)
open CryptoVerification.LibsignalTripleRatchetRepr (serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks Inputs cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib pqRecvInputs)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliRunBudgets cliRunNeeds instLsCodeInvFrozen)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost RunSem addrValOf mkSlot runAns runRel unixEpoch)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (pksmParse_lengths_le)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
  (ckx2_w2DecSigExact_groupSpec ckx2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
  (d3SlotMainFitsOneGiBOf mainEntryBudgetFitsCapOf_pqD3Recv_dom0)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (recv_rest_length_le_msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (cliDecPkCanonSlotEnvExact' cliDecPkCanonSlotEnvExact'_ghost_congr)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
  (cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom
   cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom
   fits2_zbDom0'Cum fits2_zbDom0'GrpS109 fits2_zbDom0'Live fits2_zbDom0'MaxReq fits2_zbDom0'Peak)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MainLiftGlueF3
  (cliRunSemD3ValidMatch runRel_pqRecv_validMatch)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyG2
  (h9g_decSigSlotSpecFrozenPlaced_congr_sem h9g_encSlotSpecPlaced_congr_sem)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H9PathBAssemblyHonestR2
  (h9r2_nwDom_pqD3Recv_pathB)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfPlaced slotsOfSigFrozenPlaced
   slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_GhostMainOkValidMatchK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
  (h2ka_branch2HookReplaysK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (h2kb_hole2_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
  (ghostMainSubroutineD3_of_domScopedRunTight_preFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_RunTightAt579PreFd h2ki_W1EncryptSlot464OkK h2ki_W2DecryptSignalSlot463OkK
   h2ki_W3InitSlot521OkK slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA (h2k_hole2_hioOfFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK mkF3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr hole3_initEnv_r1c_congr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hMainStk hole2_hblk hole2_hext_nodup)
open VerifiedLibraries (mallocngLib)

/-! ## Shared K Witness Handle, D3 Slot Interface, and `encrypt` / `decryptSignal` Congruences -/

/-- Closed `F3CliElfGhostWitnessK` handle at `ghFixed := h2k_ghFixedK mpl mmpl` built from
`h2ka_branch2HookReplaysK`. -/
noncomputable abbrev h2kd3_witnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl) :
    F3CliElfGhostWitnessK mpl mmpl :=
  mkF3CliElfGhostWitnessK mpl mmpl hLs hMm (h2ka_branch2HookReplaysK mpl mmpl hLs hMm)

/-- Slot-parametric Block-`579` D3 interface at `ghFixed`: composes `PksmTryFromEnv`
(Block `111`), public callees, `kemDeserialize`, and the four `slotWithPreFdsGe3Closed` contracts
(`464`, `463`, `521`, `520`) for any `S : RunSem` with `S.pksmParse = pksmParse` and any `sEnvs`
satisfying the four arm ghost congruences. -/
def h2kd3_SpineBD3SlotsRunTightAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (S : RunSem) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (sEnvs : RunSlotEnvs),
    S.pksmParse = pksmParse →
    (∀ g d2 fsp,
      sEnvs.initiate (r1cInitGhost g d2 fsp) = sEnvs.initiate (r1cInitGhost g d2 0#64)) →
    (∀ g peerV peerG meG fsp,
      peerG.val = addrValOf peerV →
      sEnvs.encrypt (r2EncGhost g peerG meG fsp) =
        sEnvs.encrypt (r2EncGhost g (r2PeerGhost0 peerV) meG 0#64)) →
    (∀ g fsp w peerV meG msgG m,
      sEnvs.decryptSignal (r3aDecSigGhost g fsp (r3aPeerGhost w peerV) meG msgG m) =
        sEnvs.decryptSignal (r3aDecSigGhost0 g peerV meG m)) →
    (∀ x y : DecPkGhost,
      x.peer.val = y.peer.val → x.me.val = y.me.val →
      x.stores = y.stores → x.coinsP = y.coinsP →
      x.F = y.F → x.coins = y.coins → x.msg = y.msg →
      sEnvs.decryptPrekey x = sEnvs.decryptPrekey y) →
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs S needs).encrypt).OkPlaced
      (lsProg_579 H) (mpl.base 464) →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs S needs).decryptSignal).OkPlaced
      (lsProg_579 H) (mpl.base 463) →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs S needs).initiate).OkPlaced
      (lsProg_579 H) (mpl.base 521) →
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs S needs).decryptPrekey).OkPlaced
      (lsProg_579 H) (mpl.base 520) →
    h2ki_RunTightAt579PreFd hblk hext_nodup H A cliBudgetLimits
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv S))
      S

abbrev h2kd3_SpineBD3SlotsRunTightK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2kd3_SpineBD3SlotsRunTightAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- `RunProofs.encDef` and `RunProofs.Agree.encDef` coincide at every `(P, Scope)`. -/
theorem h2kd3_runProofs_encDef_eq_agree (P : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) :
    CryptoVerification.SignalSession.Cli.RunProofs.encDef P Scope =
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef P Scope := by
  have hFinal : ∀ F calls,
      CryptoVerification.SignalSession.Cli.RunProofs.cliFinal F calls =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal F calls := by
    intro F calls
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliFinal
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliFinal
    have hStep :
        CryptoVerification.SignalSession.Cli.RunProofs.cliStep F =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliStep F := by
      funext g c; cases c <;> rfl
    rw [hStep]
  have hAns : ∀ F peer,
      CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers Scope F peer
        (CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer) =
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
          (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer) := by
    intro F peer
    have hKey :
        CryptoVerification.SignalSession.Cli.RunProofs.encKey Scope F peer =
          CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer := by
      unfold CryptoVerification.SignalSession.Cli.RunProofs.encKey
        CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey
      rcases loadRec Scope F peer with _ | (_ | r) <;> rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer with _ | _ <;>
      rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.encDef
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef
  rw [hAns F peer]
  generalize messageEncrypt P.C protoSignalCodec
    (pqxdhSpqrModel P).spqr (serializeAddrVals (serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
      (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer))
    ptext peer me unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

/-- Transports a `slotWithPreFdsGe3Closed` W1 (`encrypt`, Block `464`) `.OkPlaced` contract across
equal `EncEnv` and matching `(filesOk, encOk, encrypt)` `RunSem` projections. -/
theorem h2kd3_encSlotWithPreFd_congr [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {EncEnv₁ EncEnv₂ : EncGhost → List AllocEvent → Prop}
    {S₁ S₂ : RunSem} {need : Nat} {prog : Program} {entry : BitVec 64}
    (henv : EncEnv₁ = EncEnv₂)
    (hfiles : S₁.filesOk = S₂.filesOk) (hencOk : S₁.encOk = S₂.encOk)
    (henc : S₁.encrypt = S₂.encrypt)
    (h : (slotWithPreFdsGe3Closed (mkSlot (encSlotSpecPlaced A lim EncEnv₁ S₁) need)).OkPlaced
      prog entry) :
    (slotWithPreFdsGe3Closed (mkSlot (encSlotSpecPlaced A lim EncEnv₂ S₂) need)).OkPlaced
      prog entry := by
  subst henv
  intro stk hlo hhi
  have heq := h9g_encSlotSpecPlaced_congr_sem A lim EncEnv₁ S₁ S₂ stk hfiles hencOk henc
  simpa only [slotWithPreFdsGe3Closed, mkSlot, heq] using h stk hlo hhi

/-- Transports a `slotWithPreFdsGe3Closed` Frozen W2 (`decryptSignal`, Block `463`) `.OkPlaced`
contract across equal `DecSigEnv` and matching `(filesOk, decryptSignal)` `RunSem` projections. -/
theorem h2kd3_decSigFrozenSlotWithPreFd_congr [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecSigEnv₁ DecSigEnv₂ : DecSigGhost → List AllocEvent → Prop}
    {S₁ S₂ : RunSem} {need : Nat} {prog : Program} {entry : BitVec 64}
    (henv : DecSigEnv₁ = DecSigEnv₂)
    (hfiles : S₁.filesOk = S₂.filesOk) (hdecSig : S₁.decryptSignal = S₂.decryptSignal)
    (h : (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv₁ S₁) need)).OkPlaced prog entry) :
    (slotWithPreFdsGe3Closed
      (mkSlot (decSigSlotSpecFrozenPlaced A lim DecSigEnv₂ S₂) need)).OkPlaced prog entry := by
  subst henv
  intro stk hlo hhi
  have heq := h9g_decSigSlotSpecFrozenPlaced_congr_sem A lim DecSigEnv₁ S₁ S₂ stk hfiles hdecSig
  simpa only [slotWithPreFdsGe3Closed, mkSlot, heq] using h stk hlo hhi

/-! ## `validMatch` Slot-`520` Interface and `MainEntryBudgetFitsCapOf` -/

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `validMatch`) pre-only `FdsGe3Closed`
interface. -/
def h2kd3_W4ValidMatchSlot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
      (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemD3ValidMatch X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2kd3_W4ValidMatchSlot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2kd3_W4ValidMatchSlot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- `ValidMatch` D3 `RunEnv` family at `[LibsignalPlacement]`, matching `ElfTopJoinVm`. -/
noncomputable abbrev h2kd3_validMatchRunEnvAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
        cliRunBudgets (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
      PksmTryFromEnv (cliRunSemD3ValidMatch X W))

/-- `runAns` on `cliRunSemD3ValidMatch X W` coincides definitionally with `cliRunSemPathB X W`. -/
theorem h2kd3_runAns_validMatch_eq_pathB (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (i : Inputs) :
    runAns (cliRunSemD3ValidMatch X W) i = runAns (cliRunSemPathB X W) i :=
  rfl

/-- `MainEntryBudgetFitsCapOf` for D3 `validMatch` (`cliRunSemD3ValidMatch X W` +
`cliDecPkCanonSlotEnvExact' X W`), reusing `H9PathBAssemblyHonestR2.h9r2_nwDom_pqD3Recv_pathB`. -/
theorem h2kd3_fitsCap_validMatch [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W))
          PksmTryFromEnv (cliRunSemD3ValidMatch X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W))) :=
  mainEntryBudgetFitsCapOf_pqD3Recv_dom0
    (fun {M'} A' B' => cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {M'} A' B' => cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    img (cliRunSemD3ValidMatch X W) X W A cliRunBudgets
    (cliDecPkCanonSlotEnvExact' X W)
    fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109
    (fun i nw out hi ha =>
      h9r2_nwDom_pqD3Recv_pathB X W i nw out hi
        (h2kd3_runAns_validMatch_eq_pathB X W i ▸ ha))
    (fun g peerV M' A' w1R hi hp hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_phaseCredit W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun g peerV M' A' w1R hi hp hc hrep hdom => by
      have heq : cliEncryptBinaryKitSlotEnvExact W A' w1R.B =
          ckx2_cliEncryptBinaryKitSlotEnvExact W A' w1R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w1R.B)
          (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w1EncExact_groupSpec W g peerV M' A' w1R hi hp hc hrep hdom)
    (fun g peerV M' A' w2R hi hp hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w2DecSigExact_phaseCredit W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun g peerV M' A' w2R hi hp hc hrep hdom => by
      have heq : cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B =
          ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' w2R.B :=
        congrArg
          (fun (f : {M'' : AllocCostModel} → RustCliAllocBudget M'' → RunBudgets → _) => f A' w2R.B)
          (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
      rw [heq]
      exact ckx2_w2DecSigExact_groupSpec W g peerV M' A' w2R hi hp hc hrep hdom)
    (fun g meV peerV rest pm hi hp hin hc hst hpk =>
      cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom X W hi hp rfl rfl
        (Nat.le_trans (pksmParse_lengths_le hpk).2.2.1
          (recv_rest_length_le_msgCapBytes hin hc hst)))
    (by decide)
    (fun g meV peerV rest pm hi hp hin hc hst hpk =>
      cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom X W hi hp rfl rfl
        (Nat.le_trans (pksmParse_lengths_le hpk).2.2.1
          (recv_rest_length_le_msgCapBytes hin hc hst)))
    (by unfold d3SlotMainFitsOneGiBOf; decide)
    rfl

/-! ## Block-`579` to Block-`617` `validMatch` Top-Join Assemblers -/

/-- Plugs W1 (`464`), W2 (`463`), W3 (`521`), and `validMatch` W4 (`520`) into
`h2kd3_SpineBD3SlotsRunTightK` to discharge Block `579` for `cliRunSemD3ValidMatch X W`. -/
theorem h2kd3_runTight_validMatch_of_ifaces
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK w)
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4 : h2kd3_W4ValidMatchSlot520OkK w)
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    h2ki_RunTightAt579PreFd w.hblk w.hext_nodup
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (h2kd3_validMatchRunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup X W γ tp)
      (cliRunSemD3ValidMatch X W) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact' X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hEnc :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemD3ValidMatch X W) needs).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
    dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced, slotsOfPlaced,
      sEnvs, binaryKitRunSlotEnvsExact]
    exact h2kd3_encSlotWithPreFd_congr rfl rfl rfl
      (h2kd3_runProofs_encDef_eq_agree ⟨W.C, W.Q⟩ scopeIn).symm
      (hW1 h547 X W γ tp)
  have hDecSig :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemD3ValidMatch X W) needs).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
    dsimp only [slotsOfSigPkFrozenPlaced, slotsOfSigFrozenPlaced,
      sEnvs, binaryKitRunSlotEnvsExact]
    exact h2kd3_decSigFrozenSlotWithPreFd_congr rfl rfl
      (decSigDef_eq_runProofs ⟨W.C, W.Q⟩ scopeIn).symm
      (hW2 h547 X W γ tp)
  have hInit :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemD3ValidMatch X W) needs).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521) :=
    hW3 h547 X W γ tp (cliRunSemD3ValidMatch X W) sEnvs needs rfl rfl rfl rfl rfl
  exact hSpineB h547 (cliRunSemD3ValidMatch X W) W γ tp sEnvs rfl
    (hole3_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W A)
    (hole3_decSigEnv_r3a_congr W A)
    (cliDecPkCanonSlotEnvExact'_ghost_congr X W)
    hEnc hDecSig hInit (hW4 h547 X W γ tp)

/-- Pre-`hTrFrozen` `validMatch` Block-`579 → 617` lift at `h2k_ghFixedK mpl mmpl` directly from
post-slot `h2ki_RunTightAt579PreFd`. -/
theorem h2kd3_ghostMainOkValidMatchK_of_runTight
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
          (h2kd3_validMatchRunEnvAt (mmpl := mmpl)
            (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) X W γ tp)
          (cliRunSemD3ValidMatch X W)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkValidMatchK mpl mmpl := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  intro h547 X W
  refine ⟨pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3ValidMatch X W)), ?_, ?_⟩
  · exact ghostMainSubroutineD3_of_domScopedRunTight_preFd
      (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (h2k_ghFixedK mpl mmpl)
      (@instLsCodeInvFrozen
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) (cliRunSemD3ValidMatch X W)
      rfl hG (h2k_hole2_hioOfFd mpl mmpl hLs hMm W)
      hole2_hMainStk
      (fun γ tp =>
        @h2kd3_fitsCap_validMatch
          (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
          (default : Image) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
      (fun γ tp => hRun h547 X W γ tp)
  · intro st hwf body pm m rc hbody hparse hpk hm hmatch
    exact ⟨runAns (cliRunSemD3ValidMatch X W)
        (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
      runRel_pqRecv_validMatch X W st body pm m rc hwf hbody hparse hpk hm hmatch⟩

/-- Closes `h2asm_GhostMainOkValidMatchK mpl mmpl` from `h2kd3_SpineBD3SlotsRunTightK`, shared
slot contracts `464` / `463` / `521`, and `h2kd3_W4ValidMatchSlot520OkK`. -/
theorem h2kd3_ghostMainOkValidMatchK_of_ifaces
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4 : h2kd3_W4ValidMatchSlot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkValidMatchK mpl mmpl :=
  h2kd3_ghostMainOkValidMatchK_of_runTight mpl mmpl hLs hMm
    (h2kd3_runTight_validMatch_of_ifaces (h2kd3_witnessK mpl mmpl hLs hMm)
      hSpineB hW1 hW2 hW3 hW4)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
