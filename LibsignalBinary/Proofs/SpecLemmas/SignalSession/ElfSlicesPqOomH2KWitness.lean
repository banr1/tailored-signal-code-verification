/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliElf
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics

/-!
# K-Route Ghost Witness Carrier and Top-Level Arm Plumbing

Defines the `ghFixed`-parametric witness bundle `F3CliElfGhostWitnessK`, constructs it at
`h2k_ghFixedK mpl mmpl` from `h2asm_Branch2HookReplaysK`, and transfers the six ghost
block-617 `MainOk` obligations to real-code `F3CodeOk` arms and
`CliPqBinaryV2OomF3BytesPlaced cliElfBytes`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoGames.LibsignalSession (GhostState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification
  (LibsignalFrozen LibsignalPlacement libsignalMutatedBlocks libsignalSessionExterns)
open CryptoVerification.E2E
  (PEParams PreKeyMessageFields RecordExtras UnreachedPqxdhPrimitives wirePrekey)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession
  (CliHooks Inputs OutcomeMatchesModelExceptPath PqParty PqSessionMatches PqxdhPartyInSpecDomain
   cliElfBytes cliElfImage cliExternsPlaced cliProcessInputs libsignalSessionLib lsReadFileSym
   observe partyAddress pqRecvInputs pqRecvPrekeyModel pqxdhExpectedOutcome sessionFile)
open CryptoVerification.SignalSession.Cli (CommitOk MainResult RunAnswer)
open CryptoVerification.SignalSession.Cli.MainHops
  (cliIo cliMainStk cliResStack cliRunBudgets cliWrOk mainFrameSize)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.D3 (D3NoMatchSessionFile)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (MainInitSemF3G MainOkOverD3F3G MainOkPathBD3F3G MainOkUntypedD3F3G MainOkValidMatchD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (cliRunSemPathB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3 (pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (MainOkCliExtPqB2NeedLocksPlacedAt b2MainSpecTightNeedLocksFineAt cliBudgetLimits)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2G
  (F3MemsetMemcpyEntryLrFalse MainOkCliF3PqB2NeedLocksPlacedAtG
   mainOkCliF3PqG_of_block617TransferFixedG)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
  (cliProgExtPlacedAt cliStaticsPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Block617TransferG
  (Block617TransferFixedHypG)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainIoBoundedPlaced (ReadStdinBoundedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3
  (InitRunSemOk initD3ScopedRun)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeOk)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
  (h2asm_Branch2HookReplaysK h2asm_F3CliElfGhostWitnessK h2asm_GhostMainArmsK
   h2asm_cliPqBinaryV2OomF3BytesPlaced_cliElfK h2asm_hole2_hTrFrozenKG h2asm_mkGhostWitnessK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
  (h2k_CliGhostAllocHooksK h2k_CliGhostSpqrAllocHooksK h2k_CliRunHooksBundleK h2k_MainIoOfPlacedK
   h2k_ghFixedK h2k_hole2_hFsK h2k_hole2_hGSpqrK h2k_hole2_hHooksBundleK h2k_hole2_hReadSatK
   h2k_hole2_hghNoAllocK h2k_hole2_hioOfK h2k_readFileSpecK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hMainStk hole2_hPl_mng hole2_hblk hole2_hext_nodup hole2_hookStack)

/-! ## Witness Carrier `F3CliElfGhostWitnessK` -/

/-- `ghFixed`-parametric K-route counterpart of `F3CliElfGhostWitness`, packaging
`hReadSatK`, `hioOfK`, `hHooksBundleK`, and `hGSpqrK`. -/
structure F3CliElfGhostWitnessK (mpl mmpl : MultiPlacement) where
  ghFixed : CliGhostHooks
  hookStack : Nat
  hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
    (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i)
  hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup
  hPl_mng : mallocngLib.Placeable mmpl
  hMainStk : mainFrameSize + max (max extHookStack hookStack) cliResStack ≤ cliMainStk
  hTrFrozen :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    Block617TransferFixedHypG mpl mmpl
      (fun W => cliGhostExterns ghFixed (cliExternsPlaced mmpl W))
      (cliExternsPlaced mmpl) (F3MemsetMemcpyEntryLrFalse mmpl)
      (LibsignalFrozen mpl) (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk
  hGSpqrK :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostSpqrAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed
  hFs :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    CliGhostHooksFs ghFixed
  hReadSatK :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
        (h2k_readFileSpecK cliIo.rd cliWrOk
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
          cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd))
  hghNoAlloc :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none))
  hioOfK :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_MainIoOfPlacedK (libsignalPlacementOf mpl hblk hext_nodup) _
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) cliIo hookStack
        ReadStdinBoundedEnv (ReadFileRuleEnvFixed cliIo.rd)
  hHooksBundleK :
    letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
    ∀ (W : CliHooks) (γ : GhostName) (tp : BitVec 64),
      @h2k_CliRunHooksBundleK (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (ReadFileRuleEnvFixed cliIo.rd)

/-- Projects `F3CliElfGhostWitnessK.hGSpqrK` to `h2k_CliGhostAllocHooksK`. -/
theorem F3CliElfGhostWitnessK.hGK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
    ∀ (γ : GhostName) (tp : BitVec 64),
      h2k_CliGhostAllocHooksK fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits w.ghFixed :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  fun γ tp => (w.hGSpqrK γ tp).toh2k_CliGhostAllocHooksK

/-! ## Constructors at `h2k_ghFixedK` -/

/-- Lifts `h2asm_F3CliElfGhostWitnessK` to `F3CliElfGhostWitnessK` at `ghFixed := h2k_ghFixedK mpl mmpl`. -/
noncomputable def F3CliElfGhostWitnessK.ofH2Asm {mpl mmpl : MultiPlacement}
    (w0 : h2asm_F3CliElfGhostWitnessK mpl mmpl) :
    F3CliElfGhostWitnessK mpl mmpl :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl w0.hblk w0.hext_nodup
  { ghFixed := h2k_ghFixedK mpl mmpl
    hookStack := hole2_hookStack
    hblk := w0.hblk
    hext_nodup := w0.hext_nodup
    hPl_mng := w0.hPl_mng
    hMainStk := w0.hMainStk
    hTrFrozen := w0.hTrFrozen
    hGSpqrK := w0.hGSpqr
    hFs := w0.hFs
    hReadSatK := w0.hReadSat
    hghNoAlloc := w0.hghNoAlloc
    hioOfK := w0.hioOf
    hHooksBundleK := w0.hHooksBundle }

/-- Constructs `F3CliElfGhostWitnessK mpl mmpl` from `h2asm_Branch2HookReplaysK`. -/
noncomputable def mkF3CliElfGhostWitnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3CliElfGhostWitnessK mpl mmpl :=
  F3CliElfGhostWitnessK.ofH2Asm (h2asm_mkGhostWitnessK mpl mmpl hLs hMm hBranch2)

/-- Explicit field-by-field constructor for `F3CliElfGhostWitnessK` (via `h2asm_hole2_hTrFrozenKG`), definitionally equal to `mkF3CliElfGhostWitnessK`. -/
noncomputable def mkF3CliElfGhostWitnessK_of_h2k
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    F3CliElfGhostWitnessK mpl mmpl :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  { ghFixed := h2k_ghFixedK mpl mmpl
    hookStack := hole2_hookStack
    hblk := hole2_hblk mpl hLs
    hext_nodup := hole2_hext_nodup mpl hLs
    hPl_mng := hole2_hPl_mng mmpl hMm
    hMainStk := hole2_hMainStk
    hTrFrozen := h2asm_hole2_hTrFrozenKG mpl mmpl hLs hMm hBranch2
    hGSpqrK := h2k_hole2_hGSpqrK mpl mmpl hLs hMm
    hFs := h2k_hole2_hFsK mpl mmpl hLs hMm
    hReadSatK := h2k_hole2_hReadSatK mpl mmpl hLs hMm
    hghNoAlloc := h2k_hole2_hghNoAllocK mpl mmpl hLs hMm
    hioOfK := h2k_hole2_hioOfK mpl mmpl hLs hMm
    hHooksBundleK := h2k_hole2_hHooksBundleK mpl mmpl hLs hMm }

theorem mkF3CliElfGhostWitnessK_ghFixed
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2).ghFixed = h2k_ghFixedK mpl mmpl :=
  rfl

theorem mkF3CliElfGhostWitnessK_eq_of_h2k
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl) :
    mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2 =
      mkF3CliElfGhostWitnessK_of_h2k mpl mmpl hLs hMm hBranch2 :=
  rfl

/-! ## Witness-Parametric `MainOk` Arms -/

/-- `w.ghFixed`-parametric ghost block-617 counterpart of `MainOkOverD3F3`. -/
def GhostMainOkOverOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a)) ∧
      (∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (x : RecordExtras) (g : GhostState (List (BitVec 8))), st.session = some (x, g) →
        ∀ (m : PreKeyMessageFields) (rc : BitVec 256),
          m.inner.length + 2048 < 2 ^ 32 →
          ¬ PqSessionMatches x g m →
          let inp := pqRecvInputs WP st (wirePrekey :: m.bytes) rc
          ∃ a, Run inp a ∧
            (OutcomeMatchesModelExceptPath WP inp (sessionFile (partyAddress st.party.other))
               (pqRecvPrekeyModel X WP { st with session := none } m rc)
               (observe inp.files a) ∧
             D3NoMatchSessionFile X WP st x g m rc (observe inp.files a)) ∧
            CommitOk inp (MainResult.ofAnswer a))

/-- `w.ghFixed`-parametric ghost block-617 counterpart of `MainOkUntypedD3F3`. -/
def GhostMainOkUntypedOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ W : CliHooks,
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) cliProcessInputs)

/-- `w.ghFixed`-parametric ghost block-617 counterpart of `MainOkPathBD3F3`. -/
def GhostMainOkPathBOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok
        (cliProgExtPlacedAt mpl
          (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
        (mpl.base 617)
        (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
          cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
          (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) cliProcessInputs)

/-- `w.ghFixed`-parametric ghost block-617 counterpart of `MainOkValidMatchD3F3`. -/
def GhostMainOkValidMatchOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    let WP : PEParams := ⟨W.C, W.Q⟩
    ∃ Run : Inputs → RunAnswer → Prop,
      (∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            Run cliProcessInputs)) ∧
      ∀ (st : PqParty), PqxdhPartyInSpecDomain WP st →
        ∀ (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields)
          (rc : BitVec 256),
          body.length < 2 ^ 32 →
          pksmParse body = some pm →
          pkToE? pm = some m →
          m.inner.length + 2048 < 2 ^ 32 →
          (∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
          let inp := pqRecvInputs WP st (wirePrekey :: body) rc
          ∃ a, Run inp a ∧
            observe inp.files a = pqxdhExpectedOutcome WP inp (pqRecvPrekeyModel X WP st m rc) ∧
            CommitOk inp (MainResult.ofAnswer a)

/-- `w.ghFixed`-parametric ghost block-617 counterpart of `MainInitSemF3`. -/
def GhostMainInitSemOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop :=
  mpl.base 547 ≠ 0#64 →
  ∀ (X : UnreachedPqxdhPrimitives) (W : CliHooks),
    ∃ S : RunSem,
      InitRunSemOk S X ⟨W.C, W.Q⟩ ∧
      ∀ (γ : GhostName) (tp : BitVec 64),
        subroutine_ok
          (cliProgExtPlacedAt mpl
            (fun W' => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W')) 617 W)
          (mpl.base 617)
          (b2MainSpecTightNeedLocksFineAt (mallocngAddrsOfPlacement mmpl).libc (LibsignalFrozen mpl)
            (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart)
            cliBudgetLimits fineCostModel.init cliMainStk (cliStaticsPlacedAt mpl)
            (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) cliProcessInputs)

/-- Bundles the six ghost block-617 `MainOk` obligations over `w : F3CliElfGhostWitnessK mpl mmpl`. -/
structure GhostMainArmsOfWitnessK {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl) : Prop where
  hmain : MainOkCliExtPqB2NeedLocksPlacedAt mpl mmpl
    (fun W => cliGhostExterns w.ghFixed (cliExternsPlaced mmpl W))
    617 cliProcessInputs (LibsignalFrozen mpl)
    (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk cliBudgetLimits
  hoverD3 : GhostMainOkOverOfWitnessK w
  huntyped : GhostMainOkUntypedOfWitnessK w
  hpathB : GhostMainOkPathBOfWitnessK w
  hvalidMatch : GhostMainOkValidMatchOfWitnessK w
  hinitSem : GhostMainInitSemOfWitnessK w

/-- Transfers `GhostMainArmsOfWitnessK w` across `w.hTrFrozen` to the six real-code `F3CodeOk` guarded `MainOk*G` arms. -/
theorem realMainArms_of_witnessKG {mpl mmpl : MultiPlacement}
    (w : F3CliElfGhostWitnessK mpl mmpl)
    (hArms : GhostMainArmsOfWitnessK w) :
    MainOkCliF3PqB2NeedLocksPlacedAtG mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk ∧
    MainOkOverD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk ∧
    MainOkUntypedD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk ∧
    MainOkPathBD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk ∧
    MainOkValidMatchD3F3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk ∧
    MainInitSemF3G mpl mmpl (F3CodeOk mpl mmpl)
      (mallocngAddrsOfPlacement mmpl).libc cliElfImage.brkStart cliMainStk := by
  letI : LibsignalPlacement := libsignalPlacementOf mpl w.hblk w.hext_nodup
  have hTr := w.hTrFrozen
  refine ⟨mainOkCliF3PqG_of_block617TransferFixedG hTr hArms.hmain, ?_, ?_, ?_, ?_, ?_⟩
  · intro h547 X W
    obtain ⟨Run, hOk, hPost⟩ := hArms.hoverD3 h547 X W
    exact ⟨Run, hTr W Run hOk, hPost⟩
  · intro h547 W
    exact hTr W (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) (hArms.huntyped h547 W)
  · intro h547 X W
    exact hTr W (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemPathB X W))) (hArms.hpathB h547 X W)
  · intro h547 X W
    obtain ⟨Run, hOk, hPost⟩ := hArms.hvalidMatch h547 X W
    exact ⟨Run, hTr W Run hOk, hPost⟩
  · intro h547 X W
    obtain ⟨S, hSem, hOk⟩ := hArms.hinitSem h547 X W
    exact ⟨S, hSem, hTr W (initD3ScopedRun ⟨W.C, W.Q⟩ (runRel S)) hOk⟩

/-- Instantiates `h2asm_GhostMainArmsK` from `GhostMainArmsOfWitnessK` at `mkF3CliElfGhostWitnessK`. -/
theorem ghostMainArmsK_of_witnessK
    (mpl mmpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hMm : mallocngLib.LinkedAt cliElfBytes mmpl)
    (hBranch2 :
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hArms : GhostMainArmsOfWitnessK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm hBranch2)) :
    letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
    h2asm_GhostMainArmsK mpl mmpl :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
  { hmain := hArms.hmain
    hoverD3 := hArms.hoverD3
    huntyped := hArms.huntyped
    hpathB := hArms.hpathB
    hvalidMatch := hArms.hvalidMatch
    hinitSem := hArms.hinitSem }

/-- Assembles `CliPqBinaryV2OomF3BytesPlaced cliElfBytes` from `hBranch2` and `GhostMainArmsOfWitnessK`. -/
theorem cliPqBinaryV2OomF3BytesPlaced_cliElf_of_witnessArmsK
    (hBranch2 : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl),
      mallocngLib.LinkedAt cliElfBytes mmpl →
      letI : LibsignalPlacement := libsignalPlacementOf mpl (hole2_hblk mpl hLs) (hole2_hext_nodup mpl hLs)
      h2asm_Branch2HookReplaysK mpl mmpl)
    (hWitnessArms : ∀ mpl mmpl (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
      (hMm : mallocngLib.LinkedAt cliElfBytes mmpl),
      GhostMainArmsOfWitnessK (mkF3CliElfGhostWitnessK mpl mmpl hLs hMm (hBranch2 mpl mmpl hLs hMm))) :
    CliPqBinaryV2OomF3BytesPlaced cliElfBytes :=
  h2asm_cliPqBinaryV2OomF3BytesPlaced_cliElfK hBranch2
    (fun mpl mmpl hLs hMm =>
      ghostMainArmsK_of_witnessK mpl mmpl hLs hMm
        (hBranch2 mpl mmpl hLs hMm)
        (hWitnessArms mpl mmpl hLs hMm))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
