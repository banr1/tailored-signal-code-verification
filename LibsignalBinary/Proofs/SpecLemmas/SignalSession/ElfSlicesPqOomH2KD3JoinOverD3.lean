/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
public import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2

/-!
# D3 `overD3` Top-Join Assembler at `h2k_ghFixedK` (`ElfSlicesPqOomH2KD3JoinOverD3`)

**Checked by Lean.**

Defines the Slot-`520` (`decryptPrekey`) pre-only `FdsGe3Closed` interface
`h2kd3_W4OverD3Slot520Ok{At,K}` over `H7RADecPkOverValProjectedEnv`, proves
`MainEntryBudgetFitsCapOf` for `cliRunSemOverV4 X W` (`h2kd3_fitsCap_overD3`), and lifts
Block `579` to Block `617` to close `h2asm_GhostMainOkOverK mpl mmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinOverD3

open Arm64 (GhostName)
open Arm64.Obj (Image MultiPlacement)
open CryptoVerification
  (LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib pqRecvInputs)
open CryptoVerification.SignalSession.Cli.MainHops
  (RunCall cliIo cliRunBudgets cliRunNeeds instLsCodeInvFrozen)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost mkSlot runAns runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapDom0 (d3SlotMainFitsOneGiBOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact (hmx_binaryKitRunSlotEnvsSlotOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom (PostBobPrev1Dom W4RecvPrekeyCmkDom0Of')
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
  (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
   w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
  (fits2_zbDom0'Cum fits2_zbDom0'GrpS109 fits2_zbDom0'Live fits2_zbDom0'MaxReq fits2_zbDom0'Peak
   w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec')
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux (w4c_repairedStatesRecvEnvFam)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4BinaryRecvPrekeyParamsCmk w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3NonCanonValidOverPlacedBudget
  (cliRunSemOverV4 runRel_pqRecv_canonicalNoMatch runRel_pqRecv_validOver)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7OverD3SlotDom0BridgePostBob
  (DecPkD3ValidOverOfEnv' h7w_decPkValidOverTight_sub_zbDom0'FixedOf)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.H7RAOverD3Wire
  (H7RADecPkOverValProjectedEnv H7RAOut1DomPred h7ra_decPkOverValProjectedEnv_congr
   h7ra_fitsCap_overV4_of_out1Dom h7ra_initEnv_r1c_congr)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst (MainEntryBudgetFitsCapOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget (cliRunArmEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfPlaced slotsOfSigFrozenPlaced
   slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm (h2asm_GhostMainOkOverK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges (h2kb_hole2_hG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinValidMatch
  (h2kd3_SpineBD3SlotsRunTightK h2kd3_witnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3MainLiftGlue
  (ghostMainSubroutineD3_of_domScopedRunTight_preFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks (h2k_ghFixedK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KIfaces
  (h2ki_RunTightAt579PreFd h2ki_W1EncryptSlot464OkK h2ki_W2DecryptSignalSlot463OkK
   h2ki_W3InitSlot521OkK slotWithPreFdsGe3Closed)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KSpineA (h2k_hole2_hioOfFd)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
  (F3CliElfGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole2FitsEnvParts
  (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact
   hole3_decSigEnv_r3a_congr hole3_encEnv_r2_congr)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hMainStk hole2_hblk hole2_hext_nodup)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkWireStep2
  (w4s2_TryDecryptTopStateGuardedEnv w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top)
open VerifiedLibraries (mallocngLib)

/-! ## `OverD3` `RunSlotEnvs`, Slot-`520` Interface, and `MainEntryBudgetFitsCapOf` -/

/-- `RunSlotEnvs` bundle for D3 `overD3` (`ckx2` W1/W2 + `realCliInitBinarySlotEnvFixed` W3 +
`H7RADecPkOverValProjectedEnv` W4), matching `H7RAOverD3Wire.h7ra_fitsCap_overV4_of_out1Dom`. -/
noncomputable abbrev h2kd3_overD3SlotEnvs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (X : UnreachedPqxdhPrimitives) (W : CliHooks) :
    RunSlotEnvs :=
  hmx_binaryKitRunSlotEnvsSlotOf
    (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    A cliRunBudgets (realCliInitBinarySlotEnvFixed W)
    (H7RADecPkOverValProjectedEnv DecPkD3ValidOverOfEnv' A.repAlloc W X
      w4s2_TryDecryptTopStateGuardedEnv)

/-- Explicit-argument Slot-`520` (`decryptPrekey`, D3 `overD3`) pre-only `FdsGe3Closed`
interface over `h2kd3_overD3SlotEnvs`. -/
def h2kd3_W4OverD3Slot520OkAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks) : Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
    let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
    let sEnvs := h2kd3_overD3SlotEnvs A X W
    let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
    (slotWithPreFdsGe3Closed
      (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
        (cliRunSemOverV4 X W) needs).decryptPrekey).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 520)

abbrev h2kd3_W4OverD3Slot520OkK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  h2kd3_W4OverD3Slot520OkAt (mmpl := mmpl) w.hblk w.hext_nodup w.ghFixed

/-- `OverD3` `RunEnv` family at `[LibsignalPlacement]`, matching `H7RAOverD3Wire`. -/
noncomputable abbrev h2kd3_overD3RunEnvAt
    {mpl mmpl : MultiPlacement}
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (h2kd3_overD3SlotEnvs
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) X W)
      PksmTryFromEnv (cliRunSemOverV4 X W))

private noncomputable def h2kd3_overD3W4TargetEnvOf
    (_Out1Dom : H7RAOut1DomPred) (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    w4.base.peer.val = x.peer.val ∧
    w4.base.peer.name.bytes.length ≤ 40 ∧
    w4.base.files = x.F ∧
    w4.base.rd = cliIo.rd ∧
    W4RecvPrekeyCmkDom0Of'
      w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps
      sessionCapBytes msgCapBytes w4.base ∧
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
      w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w4 evs

/-- `MainEntryBudgetFitsCapOf` for D3 `overD3` (`cliRunSemOverV4 X W` + `h2kd3_overD3SlotEnvs`),
closed via `H7RAOverD3Wire.h7ra_fitsCap_overV4_of_out1Dom` at `PostBobPrev1Dom`. -/
theorem h2kd3_fitsCap_overD3 [LibsignalPlacement]
    (img : Image) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_overD3SlotEnvs A X W)
          PksmTryFromEnv (cliRunSemOverV4 X W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W))) := by
  have h :=
    h7ra_fitsCap_overV4_of_out1Dom
      img X W A PostBobPrev1Dom
      (H7RADecPkOverValProjectedEnv DecPkD3ValidOverOfEnv' A.repAlloc W X
        w4s2_TryDecryptTopStateGuardedEnv)
      h2kd3_overD3W4TargetEnvOf
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109
      (ckx2_w1EncExact_phaseCredit W)
      (ckx2_w1EncExact_groupSpec W)
      (fun g meV peerV _rest pm hi hp _hin _hc _hst _hpk hct _hp640 _hprev0 evs => by
        rintro ⟨x', hx'p, _hx'm_val, _hx'st, _hx'cp, hx'F, _hx'c, hx'msg, hevs⟩
        have hct' : x'.msg.message.ciphertext.length ≤ msgCapBytes :=
          (congrArg (fun m => m.message.ciphertext.length) hx'msg).trans_le hct
        obtain ⟨w4, hw4Dom, _hrem, _hbase, henvFixed⟩ :=
          h7w_decPkValidOverTight_sub_zbDom0'FixedOf
            (SR := w4c_repairedStatesRecvEnvFam)
            (LoopAdvEnv := CmkLoopAdvanceEvs)
            (maxOps := w4c_defaultDecodeMaxOps)
            A.repAlloc W X
            (tdEnv := fun W' => w4s2_TryDecryptTopStateGuardedEnv W')
            (fun a e hTop _hct_a he => by
              rw [w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W a hTop] at he
              exact he)
            hi hp hx'F hx'p hct' evs hevs
        obtain ⟨hpv, hp40, hfiles, hrd, hd0⟩ := hw4Dom peerV rfl
        have henvAll :
            W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
              w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w4 evs := by
          rwa [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom hi hfiles hrd]
        exact ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩)
      (fun _g _meV peerV _rest _pm hi _hp _hct _hp640 _hprev0 => by
        refine (w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' (c := .recv peerV) hi).credit.of_imp ?_
        rintro evs ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩
        refine ⟨w4, ?_, henvAll⟩
        intro p hp_eq; cases hp_eq
        exact ⟨hpv, hp40, hfiles, hrd, hd0⟩)
      (Nat.le_refl _)
      (fun _g _meV peerV _rest _pm hi _hp _hct _hp640 _hprev0 => by
        refine (w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' (c := .recv peerV) hi).groups.of_imp ?_
        rintro evs ⟨w4, hpv, hp40, hfiles, hrd, hd0, henvAll⟩
        refine ⟨w4, ?_, henvAll⟩
        intro p hp_eq; cases hp_eq
        exact ⟨hpv, hp40, hfiles, hrd, hd0⟩)
      (by unfold d3SlotMainFitsOneGiBOf; decide)
  have heq :
      cliRunArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_overD3SlotEnvs A X W) PksmTryFromEnv (cliRunSemOverV4 X W) =
        cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (h2kd3_overD3SlotEnvs A X W) PksmTryFromEnv (cliRunSemOverV4 X W) := rfl
  exact Eq.mp
    (congrArg (fun aEnvs =>
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv aEnvs)
        (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)))) heq)
    h

/-! ## Block-`579` to Block-`617` `OverD3` Top-Join Assemblers -/

/-- Plugs W1 (`464`), W2 (`463`), W3 (`521`), and `overD3` W4 (`520`) into
`h2kd3_SpineBD3SlotsRunTightK` to discharge Block `579` for `cliRunSemOverV4 X W`. -/
theorem h2kd3_runTight_overD3_of_ifaces
    {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK w)
    (hW1 : h2ki_W1EncryptSlot464OkK w)
    (hW2 : h2ki_W2DecryptSignalSlot463OkK w)
    (hW3 : h2ki_W3InitSlot521OkK w)
    (hW4 : h2kd3_W4OverD3Slot520OkK w)
    (h547 : mpl.base 547 ≠ 0#64)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    h2ki_RunTightAt579PreFd w.hblk w.hext_nodup
      (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (h2kd3_overD3RunEnvAt (mmpl := mmpl) w.hblk w.hext_nodup X W γ tp)
      (cliRunSemOverV4 X W) := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  let A := fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart
  let sEnvs := h2kd3_overD3SlotEnvs A X W
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hEncEnvEq :
      cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets =
        ckx2_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets :=
    congrArg
      (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A cliRunBudgets)
      (fits2_cliEncryptBinaryKitSlotEnvExact_eq_ckx2 W)
  have hDecSigEnvEq :
      cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets =
        ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets :=
    congrArg
      (fun (f : {M' : AllocCostModel} → RustCliAllocBudget M' → RunBudgets → _) => f A cliRunBudgets)
      (fits2_cliDecryptSignalBinaryKitSlotEnvExact_eq_ckx2 W)
  have hSpecEnc :
      encSlotSpecPlaced A cliBudgetLimits (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
          (cliRunSemD2c_placed X W) =
        encSlotSpecPlaced A cliBudgetLimits (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
          (cliRunSemOverV4 X W) := by
    funext stk
    unfold encSlotSpecPlaced
    rfl
  have hSpecDecSig :
      decSigSlotSpecFrozenPlaced A cliBudgetLimits
          (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets) (cliRunSemD2c_placed X W) =
        decSigSlotSpecFrozenPlaced A cliBudgetLimits
          (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets) (cliRunSemOverV4 X W) := by
    funext stk
    unfold decSigSlotSpecFrozenPlaced
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecPlacedOf
      LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.decSigSlotSpecBasePlaced
    rfl
  have hEnc :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemOverV4 X W) needs).encrypt).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
    change (slotWithPreFdsGe3Closed
      (mkSlot
        (encSlotSpecPlaced A cliBudgetLimits (ckx2_cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
          (cliRunSemOverV4 X W))
        needs.encrypt)).OkPlaced
      (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464)
    rw [← hEncEnvEq, ← hSpecEnc]
    exact hW1 h547 X W γ tp
  have hDecSig :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemOverV4 X W) needs).decryptSignal).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
    change (slotWithPreFdsGe3Closed
      (mkSlot
        (decSigSlotSpecFrozenPlaced A cliBudgetLimits
          (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
          (cliRunSemOverV4 X W))
        needs.decryptSignal)).OkPlaced
      (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463)
    rw [← hDecSigEnvEq, ← hSpecDecSig]
    exact hW2 h547 X W γ tp
  have hInit :
      (slotWithPreFdsGe3Closed
        (slotsOfSigPkFrozenPlaced A cliBudgetLimits sEnvs
          (cliRunSemOverV4 X W) needs).initiate).OkPlaced
        (lsProg_579 (cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))) (mpl.base 521) :=
    hW3 h547 X W γ tp (cliRunSemOverV4 X W) sEnvs needs rfl rfl rfl rfl rfl
  exact hSpineB h547 (cliRunSemOverV4 X W) W γ tp sEnvs rfl
    (h7ra_initEnv_r1c_congr W)
    (fun g peerV peerG meG fsp hp => by
      dsimp only [sEnvs, h2kd3_overD3SlotEnvs, hmx_binaryKitRunSlotEnvsSlotOf]
      rw [← hEncEnvEq]
      exact hole3_encEnv_r2_congr W A g peerV peerG meG fsp hp)
    (fun g fsp w0 peerV meG msgG m => by
      dsimp only [sEnvs, h2kd3_overD3SlotEnvs, hmx_binaryKitRunSlotEnvsSlotOf]
      rw [← hDecSigEnvEq]
      exact hole3_decSigEnv_r3a_congr W A g fsp w0 peerV meG msgG m)
    (h7ra_decPkOverValProjectedEnv_congr DecPkD3ValidOverOfEnv' A.repAlloc W X
      w4s2_TryDecryptTopStateGuardedEnv)
    hEnc hDecSig hInit (hW4 h547 X W γ tp)

/-- Pre-`hTrFrozen` `overD3` Block-`579 → 617` lift at `h2k_ghFixedK mpl mmpl` directly from
post-slot `h2ki_RunTightAt579PreFd`. -/
theorem h2kd3_ghostMainOkOverD3K_of_runTight
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
          (h2kd3_overD3RunEnvAt (mmpl := mmpl)
            (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) X W γ tp)
          (cliRunSemOverV4 X W)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkOverK mpl mmpl := by
  letI : LibsignalPlacement :=
    libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  have hG := h2kb_hole2_hG mpl mmpl hLs hMm
  intro h547 X W
  refine ⟨pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemOverV4 X W)), ?_, ?_, ?_⟩
  · exact ghostMainSubroutineD3_of_domScopedRunTight_preFd
      (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs) (h2k_ghFixedK mpl mmpl)
      (@instLsCodeInvFrozen
        (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)))
      (CliPqOrD3RecvInputs ⟨W.C, W.Q⟩) (cliRunSemOverV4 X W)
      rfl hG (h2k_hole2_hioOfFd mpl mmpl hLs hMm W)
      hole2_hMainStk
      (fun γ tp =>
        @h2kd3_fitsCap_overD3
          (libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs))
          (default : Image) X W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart))
      (fun γ tp => hRun h547 X W γ tp)
  · intro st hst x g hsess body pm m rc hbody hparse hpk hm hnomatch
    exact ⟨runAns (cliRunSemOverV4 X W)
        (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: body) rc),
      runRel_pqRecv_validOver X W st x g body pm m rc hst hsess hbody hparse hpk hm hnomatch⟩
  · intro st hst x g hsess m rc hm hnomatch
    exact ⟨runAns (cliRunSemOverV4 X W)
        (pqRecvInputs ⟨W.C, W.Q⟩ st (wirePrekey :: m.bytes) rc),
      runRel_pqRecv_canonicalNoMatch X W st x g m rc hst hsess hm hnomatch⟩

/-- Closes `h2asm_GhostMainOkOverK mpl mmpl` from `h2kd3_SpineBD3SlotsRunTightK`, shared slot
contracts `464` / `463` / `521`, and `h2kd3_W4OverD3Slot520OkK`. -/
theorem h2kd3_ghostMainOkOverD3K_of_ifaces
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hSpineB : h2kd3_SpineBD3SlotsRunTightK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW1 : h2ki_W1EncryptSlot464OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW2 : h2ki_W2DecryptSignalSlot463OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW3 : h2ki_W3InitSlot521OkK (h2kd3_witnessK mpl mmpl hLs hMm))
    (hW4 : h2kd3_W4OverD3Slot520OkK (h2kd3_witnessK mpl mmpl hLs hMm)) :
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainOkOverK mpl mmpl :=
  h2kd3_ghostMainOkOverD3K_of_runTight mpl mmpl hLs hMm
    (h2kd3_runTight_overD3_of_ifaces (h2kd3_witnessK mpl mmpl hLs hMm)
      hSpineB hW1 hW2 hW3 hW4)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KD3JoinOverD3
