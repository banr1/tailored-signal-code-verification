/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.CliF3MainOkBridge
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrExactEnvDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTightGlue
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W2InnerTight
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux

/-!
# Outer Block-579 `signal_session::run` Composition and Callee Slot Cut

**Checked by Lean.**

Reduces the placed block-579 `signal_session::run` specification (`runSpecTightPlaced`)
under `LibsignalFrozen` and `CanonicalOrFallbackPksmEnv PksmTryFromEnv` to the four
inner callee slot contracts (`hole3_w1_inner`, `hole3_w2_inner`, `hole3_w3_init`, and
`hole3_w4_decPk`), discharging placement, block-111 `PreKeySignalMessage::try_from`,
ghost-argument congruence, and `CliPubCalleesFrozenPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.style.haveILetI false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut

open Arm64 (GhostName HookSat subroutine_ok)
open Arm64.Obj (MultiPlacement)
open VerifiedLibraries (mallocngLib)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalFrozen LibsignalFullPlacement LibsignalPlacement libsignalMutatedBlocks
   libsignalSessionExterns lsmpl)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliElfBytes cliElfImage cliExternsPlaced libsignalSessionLib lsReadFileSym)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliResStack cliRunBudgets cliRunNeeds cliWrOk mProgPlaced)
open CryptoVerification.SignalSession.Cli.Run.Placed (lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost PksmGhost addrValOf mkSlot runRel)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks CliGhostHooksFs cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs (cliDecryptPrekeyNeed)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (encodeInjOn_deserializeScopeP_Q scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel fineHookRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget (SpqrSendCoinsExactEnv)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (cliMainArmEnvs cliRunCalleesEnvs)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinkedBase (DecPkD2cSlotOkFrozenPlaced)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Defs
  (m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'_ghost_congr)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed decBinaryIdKitPlacedBudgetFixed
   decBinarySessKitPlacedBudgetFixed realCliInitBinarySlotEnvFixed
   w1BinaryIdKitPlacedBudgetFixed w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemSlots (CanonicalOrFallbackPksmEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RealTdEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (PksmCanonSliceEnv subroutine_ok_preKeyTryFromPlaced_canonSlice)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromStoreCallEnv
   FromTrustedEnv FromTrustedFalseEnv FromTrustedTrueEnv LoadPollStepEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (FromApplyEnv FromCmEnv FromCurEnv FromKeyEnv FromOtrEnv FromSaveEnv PreKeyPostEncryptEnv
   WithStoresEncEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (ExternNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.HopsPlacedBudget (runSpecTightPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (w2IdVt_placed_ok w2SessVt_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommitPlacedBudget
  (runNeed_cli_le_resStack_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.AllPlacedBudget
  (cliRunArmEnvs runArmsFrozenPlaced_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cProofPlacedBudget (r1cInitGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2ProofPlacedBudget
  (r2EncGhost r2PeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aProofPlacedBudget
  (r3aDecSigGhost r3aDecSigGhost0 r3aPeerGhost r3aPeerGhost0)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchDefsPlacedBudget
  (PksmSlotOkPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkNoMatchPlacedBudget
  (CliInitSlotOkPlaced CliPubCalleesFrozenPlaced CliRunHooksBundle
   cliPubCallees_d2c_frozen_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunEnv run_ok_frozen_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs decSigSlotSpecFrozenPlaced encSlotSpecPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmLoopEnv PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromInstPlacedBudget
  (codecHooksPlaced_cli subsetA4PksmTryFromPlaced_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (cliPksmTryFrom_placed_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (InnerDecryptFrozenPlacedOk decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptSignalPlacedBudget
  (cliDecryptSignal_slotOk_full_placed decSigDef_eq_runProofs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlacedBudget
  (W1InnerPlacedOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptPlacedBudget
  (cliEncrypt_slotOk_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KemDeserializeSlotPlacedBudget
  (hc_kemDeserialize_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (readFileSpecPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3PksmAux (pksmSlotOkPlacedAt_canonOrFallback)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3InitAux (w3m_hole3_w3_init)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (SpqrSendBudgetEnv)

/-! ## Named Binary-Kit Slot Envelopes -/

/-- Binary-kit W1 (`encrypt`) slot allocator envelope (`maxOps = 109`), guarded by
`PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`. Outside the guard the predicate is
`fun _ => True`, which is sound because `FitsEnv M lim st (fun _ => True)` is
unsatisfiable at finite `lim`; outer `MainOk` callers discharge `PeerSpqrStateTight640`. -/
noncomputable def cliEncryptBinaryKitSlotEnvExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets) :
    EncGhost → List AllocEvent → Prop :=
  let sendEnv : SpqrSendBudgetEnv :=
    LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst.hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv
      W.C.F W.Q.K
      (fun _ => LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges.tlb_DecodeStateTightEnv)
      (fun _ => LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec.StatesFromPbTightEnv)
  fun x evs =>
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K x.F x.peer.val →
      CliEncryptSlotEnv ⟨W.C, W.Q⟩ A B sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

/-- Binary-kit W2 (`decryptSignal`) slot allocator envelope (`maxOps = 109`), guarded by
`PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`. Outside the guard the predicate is
`fun _ => True`, which is unsatisfiable under `FitsEnv` at finite `lim`. -/
noncomputable def cliDecryptSignalBinaryKitSlotEnvExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets) :
    DecSigGhost → List AllocEvent → Prop :=
  fun x evs =>
    LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.PeerSpqrStateTight640
        W.C.F W.Q.K x.F x.peer.val →
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A B
        (LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
          109 W.C W.Q.K)
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B)
        x evs

/-- Assembles `RunSlotEnvs` from `cliEncryptBinaryKitSlotEnvExact`, `cliDecryptSignalBinaryKitSlotEnvExact`, `InitEnv`, and `DecPkEnv`. -/
noncomputable def binaryKitRunSlotEnvsExact [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets := cliRunBudgets)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (DecPkEnv : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := cliEncryptBinaryKitSlotEnvExact W A B
  decryptSignal := cliDecryptSignalBinaryKitSlotEnvExact W A B
  initiate := InitEnv
  decryptPrekey := DecPkEnv

/-- `RunEnv` abbreviation over `binaryKitRunSlotEnvsExact`, `cliDecPkCanonSlotEnvExact`, and `CanonicalOrFallbackPksmEnv FallbackEnv`. -/
abbrev canonOrFallbackRunEnvExact
    (FallbackEnv : PksmGhost → List AllocEvent → Prop)
    (mpl mmpl : MultiPlacement) (brkStart : BitVec 64)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64) :
    RunCall → List AllocEvent → Prop :=
  letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  RunEnv
    (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W (fineHookRustCliAllocBudget γ mmpl tp brkStart) cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
      (CanonicalOrFallbackPksmEnv FallbackEnv)
      (cliRunSemD2c_placed X W))

/-! ## `LibsignalFullPlacement` from `LinkedAt cliElfBytes` -/

/-- Constructs `LibsignalFullPlacement` from `libsignalSessionLib.LinkedAt cliElfBytes mpl` with underlying `libsignalPlacementOf mpl hblk hext_nodup`. -/
@[instance_reducible]
def libsignalFullPlacementOf (mpl : MultiPlacement)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup) : LibsignalFullPlacement where
  toLibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
  placeable := hLs.choose_spec.2.1

/-! ## Block-111 `PreKeySignalMessage::try_from` Slot Witness -/

/-- Block-111 `PreKeySignalMessage::try_from` slot witness for `CanonicalOrFallbackPksmEnv PksmTryFromEnv`. -/
theorem hole3_pksmSlotOk_canonOrFallback [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (_hG : CliGhostAllocHooks M A lim gh) :
    PksmSlotOkPlacedAt (cliGhostExterns gh (cliExternsPlaced mmpl W)) A lim
      (CanonicalOrFallbackPksmEnv PksmTryFromEnv) := by
  exact pksmSlotOkPlacedAt_canonOrFallback (codecHooksPlaced_cli mmpl gh W _hG)

theorem hole3_pksmTryFromEnv_congr (x y : PksmGhost) (hb : x.bytes = y.bytes) :
    PksmTryFromEnv x = PksmTryFromEnv y := by
  have hloop : PksmLoopEnv x = PksmLoopEnv y := by
    funext evs; dsimp [PksmLoopEnv]; rw [hb]
  funext evs; apply propext; constructor
  · intro h
    cases h with
    | nil => exact .nil
    | loopOnly hcons hge hle hl =>
      exact .loopOnly (hb.symm.trans hcons) hge hle (hloop ▸ hl)
    | loopAfter hcons hge hle hl ha =>
      exact .loopAfter (hb.symm.trans hcons) hge hle (hloop ▸ hl) (hb ▸ ha)
  · intro h
    cases h with
    | nil => exact .nil
    | loopOnly hcons hge hle hl =>
      exact .loopOnly (hb.trans hcons) hge hle (hloop.symm ▸ hl)
    | loopAfter hcons hge hle hl ha =>
      exact .loopAfter (hb.trans hcons) hge hle (hloop.symm ▸ hl) (hb.symm ▸ ha)

theorem hole3_canonOrFallbackPksmEnv_congr (x y : PksmGhost) (hb : x.bytes = y.bytes) :
    CanonicalOrFallbackPksmEnv PksmTryFromEnv x = CanonicalOrFallbackPksmEnv PksmTryFromEnv y := by
  funext evs
  dsimp [CanonicalOrFallbackPksmEnv]
  rw [hb, hole3_pksmTryFromEnv_congr x y hb]

/-! ## Ghost Congruence and `CliPubCalleesFrozenPlaced` -/

theorem hole3_initEnv_r1c_congr (W : CliHooks) (gc : RunCall)
    (d2 : CryptoVerification.SignalSession.Cli.RunCompose.Init2Data) (fsp : BitVec 64) :
    realCliInitBinarySlotEnvFixed W (r1cInitGhost gc d2 fsp) =
      realCliInitBinarySlotEnvFixed W (r1cInitGhost gc d2 0#64) := by
  funext evs
  apply propext
  constructor
  · rintro ⟨w, hx, hF, ha, hgv, hab, hevs⟩
    refine ⟨{ w with x := r1cInitGhost gc d2 0#64 }, rfl, hF, ha, hgv, hab, ?_⟩
    unfold W3InitBinaryKitSlotEnvFixed at hevs ⊢
    rw [hx] at hevs
    exact hevs
  · rintro ⟨w, hx, hF, ha, hgv, hab, hevs⟩
    refine ⟨{ w with x := r1cInitGhost gc d2 fsp }, rfl, hF, ha, hgv, hab, ?_⟩
    unfold W3InitBinaryKitSlotEnvFixed at hevs ⊢
    rw [hx] at hevs
    exact hevs

private theorem h3c_seqEnv_congr {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : P₁ = P₂) (hQ : Q₁ = Q₂) :
    LibsignalBinary.Heap.SeqEnv P₁ Q₁ = LibsignalBinary.Heap.SeqEnv P₂ Q₂ := by
  rw [hP, hQ]

private theorem h3c_or_congr {A₁ A₂ B₁ B₂ : Prop} (hA : A₁ = A₂) (hB : B₁ = B₂) :
    (A₁ ∨ B₁) = (A₂ ∨ B₂) := by
  rw [hA, hB]

private theorem h3c_and_congr {A₁ A₂ B₁ B₂ : Prop} (hA : A₁ = A₂) (hB : B₁ = B₂) :
    (A₁ ∧ B₁) = (A₂ ∧ B₂) := by
  rw [hA, hB]

private theorem h3c_exists_congr {α : Sort _} {P Q : α → Prop} (h : ∀ a, P a = Q a) :
    (∃ a, P a) = (∃ a, Q a) :=
  congrArg Exists (funext h)

private theorem h3c_stringCloneEnv_eq {a b : AddrGhost} (h : a.val = b.val) :
    StringCloneEnv a.name = StringCloneEnv b.name := by
  have hb : a.name.bytes = b.name.bytes := congrArg AddrVal.name h
  funext evs
  unfold StringCloneEnv
  rw [hb]

private theorem h3c_serializeAddresses_eq (l : AddrGhost) {a b : AddrGhost}
    (h : a.val = b.val) :
    CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) l a =
      CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
        (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse) l b := by
  have hb : a.name.bytes = b.name.bytes := congrArg AddrVal.name h
  have hd : a.device = b.device := congrArg AddrVal.device h
  unfold CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
  rw [hb, hd]

private theorem h3c_otrEncryptCoreEnv_eq (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (ot : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (loc : Option AddrGhost) {a b : AddrGhost}
    (rest : List (BitVec 8)) (h : a.val = b.val) :
    LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.OtrEncryptCoreEnv
        P.C (pqxdhSpqrModel P) sendEnv uuidTryParse ot ptext loc a rest =
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.OtrEncryptCoreEnv
        P.C (pqxdhSpqrModel P) sendEnv uuidTryParse ot ptext loc b rest := by
  have hsm : ∀ pqrKey pqrMsg,
      LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv uuidTryParse
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a) =
        LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv uuidTryParse
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b) := by
    intro pqrKey pqrMsg
    have haddr :
        (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a).addresses uuidTryParse =
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b).addresses uuidTryParse := by
      cases loc with
      | none => rfl
      | some l => exact h3c_serializeAddresses_eq l h
    have hproto :
        (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc a).protoMsg uuidTryParse =
          (LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget.otrSignalMsgGhost
            P.C ot pqrKey pqrMsg ptext loc b).protoMsg uuidTryParse := by
      unfold CryptoVerification.LibsignalTripleRatchet.SignalMessageNewGhost.protoMsg
      rw [haddr]
      rfl
    funext evs
    unfold LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.SignalMessageNewEnv
      LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget.signalMessageNewEvents
    rw [haddr, hproto]
    rfl
  funext evs
  exact congrFun
    (h3c_seqEnv_congr rfl (funext fun evs' => by
      cases (pqxdhSpqrModel P).send ot.pqrState rest with
      | none => rfl
      | some v =>
        rcases v with ⟨_, pqrKey, pqrMsg⟩
        exact congrFun
          (h3c_seqEnv_congr rfl
            (h3c_seqEnv_congr rfl (h3c_seqEnv_congr (hsm pqrKey pqrMsg) rfl)))
          evs'))
    evs

private theorem h3c_ppe_congr
    (C : CryptoGames.LibsignalSession.Crypto)
    (S : CryptoVerification.LibsignalTripleRatchet.SpqrModel)
    (sess : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8)))
    (otr : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)))
    (items : CryptoGames.LibsignalSessionApi.PendingPreKey)
    (ptext : List (BitVec 8)) {ad₁ ad₂} (rest : List (BitVec 8))
    {C₁ C₂ : CryptoGames.LibsignalSession.OutgoingTripleRatchet (List (BitVec 8)) →
      List AllocEvent → Prop}
    (had : ad₁ = ad₂) (hC : ∀ o, C₁ o = C₂ o) (evs' : List AllocEvent) :
    (let res := CryptoGames.LibsignalSession.Mut.exec
      (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₁ rest) otr
    LibsignalBinary.Heap.FreeOnlyEvs evs' ∨
    match res.1 with
    | .error _ => False
    | .ok sm =>
      LibsignalBinary.Heap.SeqEnv
        (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyMsgNewRawEnv
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.pendingKyberPayload sess)
          sm.serialized.length
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.preKeyMsgFromItems
            sess items res.2 sm).serialized.length)
        (fun evs'' => LibsignalBinary.Heap.FreeOnlyEvs evs'' ∨ C₁ res.2 evs'') evs') =
    (let res := CryptoGames.LibsignalSession.Mut.exec
      (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₂ rest) otr
    LibsignalBinary.Heap.FreeOnlyEvs evs' ∨
    match res.1 with
    | .error _ => False
    | .ok sm =>
      LibsignalBinary.Heap.SeqEnv
        (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyMsgNewRawEnv
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.pendingKyberPayload sess)
          sm.serialized.length
          (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.preKeyMsgFromItems
            sess items res.2 sm).serialized.length)
        (fun evs'' => LibsignalBinary.Heap.FreeOnlyEvs evs'' ∨ C₂ res.2 evs'') evs') := by
  subst had
  dsimp only
  cases (CryptoGames.LibsignalSession.Mut.exec
    (CryptoGames.LibsignalSession.OutgoingTripleRatchet.encrypt C
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec S.spqr ptext ad₁ rest) otr).1 with
  | error _ => rfl
  | ok sm => simp only [hC]

theorem hole3_encEnv_r2_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (gc : RunCall) (peerV : AddrV) (peerG meG : AddrGhost) (fsp : BitVec 64)
    (_hp : peerG.val = addrValOf peerV) :
    cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets (r2EncGhost gc peerG meG fsp) =
      cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets
        (r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r2EncGhost gc peerG meG fsp
  let x₂ := r2EncGhost gc (r2PeerGhost0 peerV) meG 0#64
  let y₁ := CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1EncGhost x₁
  let y₂ := CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1EncGhost x₂
  let kit₁ := w1SessKitPlaced A.repAlloc cliRunBudgets x₁.F x₁.peer
  let kit₂ := w1SessKitPlaced A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ke₁ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer)
  let ke₂ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsKitEnv
    (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer)
  let ikit₁ := w1IdKitPlaced A.repAlloc cliRunBudgets x₁.F x₁.peer
  let ikit₂ := w1IdKitPlaced A.repAlloc cliRunBudgets x₂.F x₂.peer
  let ike₁ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer)
  let ike₂ := LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux.toTempTwinsIkitEnv
    (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer)
  let st0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
  let ist0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
  have hy_val : y₁.rem.val = y₂.rem.val := _hp
  have hsc : StringCloneEnv y₁.rem.name = StringCloneEnv y₂.rem.name :=
    h3c_stringCloneEnv_eq hy_val
  have hload : ke₁.loadPollEnv st0 y₁.rem.val = ke₂.loadPollEnv st0 y₂.rem.val :=
    congrArg (ke₂.loadPollEnv st0) hy_val
  have hscope : ∀ r, kit₁.ScopeAt scopeKit st0 y₁.rem.val r = kit₂.ScopeAt scopeKit st0 y₂.rem.val r :=
    fun r => congrFun (congrArg (kit₂.ScopeAt scopeKit st0) hy_val) r
  have htrust : ∀ k, ike₁.trustPollEnv ist0 y₁.rem.val k .sending =
      ike₂.trustPollEnv ist0 y₂.rem.val k .sending :=
    fun k => congrArg (fun v => ike₂.trustPollEnv ist0 v k .sending) hy_val
  have hsave : ∀ k, ike₁.savePollEnv (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁.rem.val k =
      ike₂.savePollEnv (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂.rem.val k :=
    fun k => congrArg (fun v => ike₂.savePollEnv ist0 v k) hy_val
  have hstore : ∀ r, ke₁.storePollEnv st0 y₁.rem.val r = ke₂.storePollEnv st0 y₂.rem.val r :=
    fun r => congrArg (fun v => ke₂.storePollEnv st0 v r) hy_val
  have htrust_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.TrustStepEnv
          ikit₁ ike₁ ist0 y₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.TrustStepEnv
          ikit₂ ike₂ ist0 y₂.rem.val k :=
    fun k => h3c_seqEnv_congr rfl (h3c_seqEnv_congr (htrust k) rfl)
  have hsave_step : ∀ k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SaveStepEnv
          ikit₁ ike₁ (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁.rem.val k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SaveStepEnv
          ikit₂ ike₂ (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂.rem.val k :=
    fun k => h3c_seqEnv_congr rfl (h3c_seqEnv_congr (hsave k) rfl)
  have happly : ∀ sess otr' taken,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromApplyEnv
          kit₁ ke₁ st0 y₁ sess otr' taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromApplyEnv
          kit₂ ke₂ st0 y₂ sess otr' taken :=
    fun _ _ _ => h3c_seqEnv_congr rfl (h3c_seqEnv_congr rfl (h3c_seqEnv_congr (hstore _) rfl))
  have hfromSave : ∀ sess otr' taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromSaveEnv
          kit₁ ke₁ st0 ikit₁ ike₁
          (ikit₁.trustUpdate ist0 y₁.rem.val k .sending (.ok true)) y₁ sess otr' taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromSaveEnv
          kit₂ ke₂ st0 ikit₂ ike₂
          (ikit₂.trustUpdate ist0 y₂.rem.val k .sending (.ok true)) y₂ sess otr' taken k :=
    fun sess otr' taken k =>
      h3c_seqEnv_congr (hsave_step k)
        (funext fun evs => h3c_or_congr rfl (congrFun (happly sess otr' taken) evs))
  have hcm : ∀ sess otr' taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromCmEnv
          kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr' taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromCmEnv
          kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr' taken k :=
    fun sess otr' taken k =>
      h3c_seqEnv_congr (htrust_step k)
        (funext fun evs =>
          h3c_or_congr rfl
            (h3c_or_congr
              (congrFun (h3c_seqEnv_congr hsc rfl) evs)
              (congrFun (hfromSave sess otr' taken k) evs)))
  have hppe : ∀ sess otr taken k items,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv
          P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken k items =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.PreKeyPostEncryptEnv
          P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken k items :=
    fun sess otr taken k items => funext fun evs' =>
      h3c_ppe_congr P.C (pqxdhSpqrModel P) sess otr items y₁.ptext y₁.rest
        (h3c_serializeAddresses_eq y₁.loc hy_val) (fun o => hcm sess o taken k) evs'
  let sendEnv : SpqrSendBudgetEnv :=
    LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst.hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv
      W.C.F W.Q.K
      (fun _ => LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges.tlb_DecodeStateTightEnv)
      (fun _ => LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec.StatesFromPbTightEnv)
  have hkey : ∀ sess otr taken k,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken k =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromKeyEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken k :=
    fun sess otr taken k => funext fun evs =>
      h3c_or_congr
        (h3c_and_congr rfl
          (congrFun
            (h3c_seqEnv_congr
              (h3c_otrEncryptCoreEnv_eq P sendEnv otr y₁.ptext none y₁.rest hy_val)
              (funext fun evs' => h3c_or_congr rfl (congrFun (hcm sess _ taken k) evs')))
            evs))
        (h3c_exists_congr fun items =>
          h3c_and_congr rfl
            (h3c_or_congr
              (congrFun (h3c_seqEnv_congr hsc rfl) evs)
              (congrFun
                (h3c_seqEnv_congr rfl
                  (h3c_seqEnv_congr
                    (h3c_otrEncryptCoreEnv_eq P sendEnv otr y₁.ptext (some y₁.loc) y₁.rest hy_val)
                    (hppe sess otr taken k items)))
                evs)))
  have hotr : ∀ sess otr taken,
      LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 y₁ sess otr taken =
        LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.FromOtrEnv
          P.C (pqxdhSpqrModel P) sendEnv uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 y₂ sess otr taken :=
    fun sess otr taken => funext fun evs =>
      h3c_or_congr rfl
        (h3c_exists_congr fun k =>
          h3c_and_congr rfl (congrFun (hkey sess otr taken k) evs))
  have hinner :
      CliEncryptSlotEnv P A cliRunBudgets sendEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x₁ =
        CliEncryptSlotEnv P A cliRunBudgets sendEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x₂ := by
    funext evs
    exact congrFun
      (h3c_seqEnv_congr
        (h3c_seqEnv_congr rfl (h3c_seqEnv_congr hload rfl))
        (funext fun evs₁ =>
          h3c_or_congr rfl
            (h3c_or_congr
              (congrFun (h3c_seqEnv_congr hsc rfl) evs₁)
              (congrFun
                (h3c_seqEnv_congr rfl
                  (funext fun evs' =>
                    h3c_or_congr rfl
                      (h3c_exists_congr fun r =>
                        h3c_exists_congr fun sess =>
                          h3c_exists_congr fun otr =>
                            h3c_exists_congr fun taken =>
                              h3c_and_congr (hscope r)
                                (h3c_and_congr rfl
                                  (h3c_and_congr rfl
                                    (congrFun (hotr sess otr taken) evs'))))))
                evs₁))))
      evs
  have hF : x₁.F = x₂.F := rfl
  have hp : x₁.peer.val = x₂.peer.val := _hp
  funext evs
  unfold cliEncryptBinaryKitSlotEnvExact
  rw [hF, hp, congrFun hinner evs]

theorem hole3_decSigEnv_r3a_congr [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M)
    (gc : RunCall) (fsp : BitVec 64)
    (w) (peerV : AddrV) (meG : AddrGhost) (msgG) (m) :
    cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets
        (r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m) =
      cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets
        (r3aDecSigGhost0 gc peerV meG m) := by
  let P : PEParams := ⟨W.C, W.Q⟩
  let x₁ := r3aDecSigGhost gc fsp (r3aPeerGhost w peerV) meG msgG m
  let x₂ := r3aDecSigGhost0 gc peerV meG m
  let TdEnv := LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf
    109 W.C W.Q.K
  have hF : x₁.F = x₂.F := rfl
  have hp : x₁.peer.val = x₂.peer.val := rfl
  have hTd : ∀ (a₁ a₂ : LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.TryDecryptEnvArgs),
      a₁.G = a₂.G → a₁.st = a₂.st →
      a₁.rem.name.bytes = a₂.rem.name.bytes → a₁.rem.device = a₂.rem.device →
      a₁.loc.name.bytes = a₂.loc.name.bytes → a₁.loc.device = a₂.loc.device →
      a₁.msg = a₂.msg → a₁.msgType = a₂.msgType → a₁.rest = a₂.rest →
      TdEnv a₁ = TdEnv a₂ := by
    intro a₁ a₂ hG hst hrem_b hrem_d hloc_b hloc_d hmsg hmt hrest
    dsimp only [TdEnv,
      LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedEnvOf]
    unfold LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.TryDecryptCliLinkedLoopEnvOf
    rw [hst, hG]
    cases CryptoGames.LibsignalSession.Mut.exec
      CryptoGames.LibsignalSession.TripleRatchet.fromSessionState a₂.st with
    | mk res st1 =>
      cases res with
      | error _ => rfl
      | ok tr0 =>
        dsimp only
        let g₁ := LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptEnvArgsToGhost a₁
        let g₂ := LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked.tryDecryptEnvArgsToGhost a₂
        let S := CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K
        let s4Env := LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.tryDecryptCmkSeg4EnvOf
          LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget.CmkLoopAdvanceEvs
          LibsignalBinary.Heap.SpecBudget.FmtWriteEnv
        let RecvBytesEnv :=
          LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.SpqrRecvC07C09aBytesEnvOf
            109 W.C.F W.Q.K
        let fmtEnv := LibsignalBinary.Heap.SpecBudget.FormatInnerEnv
        have hrem_b' : g₁.rem.name.bytes = g₂.rem.name.bytes := hrem_b
        have hrem_d' : g₁.rem.device = g₂.rem.device := hrem_d
        have hloc_b' : g₁.loc.name.bytes = g₂.loc.name.bytes := hloc_b
        have hloc_d' : g₁.loc.device = g₂.loc.device := hloc_d
        have hmsg' : g₁.msg = g₂.msg := hmsg
        have hmt' : g₁.msgType = g₂.msgType := hmt
        have hrest' : g₁.rest = g₂.rest := hrest
        have hs4 : s4Env g₁ = s4Env g₂ := by
          funext trG tr ck
          dsimp only [s4Env]
          unfold LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf.tryDecryptCmkSeg4EnvOf
          rw [hmsg']
        have hser :
            CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
                (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
                g₁.rem g₁.loc =
              CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
                (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse)
                g₂.rem g₂.loc := by
          unfold CryptoVerification.LibsignalTripleRatchetRepr.serializeAddresses
          rw [hrem_b', hrem_d', hloc_b', hloc_d']
        have hs3 :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C g₂ := by
          funext trG tr
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3EnvOf
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore.s3CommitDefaultEnv
          dsimp only
          rw [hmsg', hrest']
        have hs5 :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                S RecvBytesEnv fmtEnv g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                S RecvBytesEnv fmtEnv g₂ := by
          funext tr
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
          rw [hmsg']
        have hs7 :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                W.C.F uuidTryParse g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                W.C.F uuidTryParse g₂ := by
          funext tr mks newPqrState
          have hv :
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.vmacEvents
                  W.C.F uuidTryParse g₁ tr mks =
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.vmacEvents
                  W.C.F uuidTryParse g₂ tr mks := by
            unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.vmacEvents
              LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget.verifyMacWithAddressesEvents
            dsimp only
            rw [hmsg', hser]
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
          rw [hv]
        have hs8 :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env g₂ := by
          funext mks newPqrState
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
          rw [hmsg']
        have hs8g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS8GenEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS8GenEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1' mks newPqrState
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS8GenEnv
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env
          rw [hmsg', hs8]
        have hs7g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS7GenEnv
                W.C uuidTryParse
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS7GenEnv
                W.C uuidTryParse
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1' mks newPqrState
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS7GenEnv
          rw [hmsg', hser, hs7, hs8g]
        have hs6g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS6GenEnv
                W.C uuidTryParse
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS6GenEnv
                W.C uuidTryParse
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1' mkg newPqrState pqrKey
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS6GenEnv
          rw [hs7g]
        have hs5g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1' mkg
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS5GenEnv
          rw [hmsg', hs5, hs6g]
        have hs4g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1' ck
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS4GenEnv
          rw [hmsg', hmt', hs4, hs5g]
        have hs3g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1'
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS3GenEnv
          rw [hmsg', hrest', hs3, hs4g]
        have hs2g :
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS2GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₁ =
              LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS2GenEnv
                W.C uuidTryParse S
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.stdAesOpt W.C)
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore.s3DefaultEnv W.C)
                s4Env
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs.PqRecvEnv
                  S RecvBytesEnv fmtEnv)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget.s6FreeOnlyEnv
                (LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux.s7Env
                  W.C.F uuidTryParse)
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux.s8Env
                LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux.s9Env g₂ := by
          funext trG tr st1'
          unfold LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.FromS2GenEnv
          rw [hmsg', hs4g, hs3g]
        exact h3c_seqEnv_congr rfl
          (congrFun (congrFun (congrFun hs2g
            (LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux.s1InitTrGhost a₂.G))
            tr0) st1)
  have hinner :
      CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets TdEnv
          (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x₁ =
        CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A cliRunBudgets TdEnv
          (decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets) x₂ := by
    let z₁ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₁
    let z₂ := CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.toDecryptGhost x₂
    let kit₁ := decSessKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
    let kit₂ := decSessKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
    let ke₁ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
    let ke₂ := decBinarySessKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
    let ikit₁ := decIdKitPlaced A.repAlloc x₁.F x₁.peer cliRunBudgets
    let ikit₂ := decIdKitPlaced A.repAlloc x₂.F x₂.peer cliRunBudgets
    let ike₁ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₁.F x₁.peer
    let ike₂ := decBinaryIdKitPlacedBudgetFixed A.repAlloc cliRunBudgets x₂.F x₂.peer
    let st0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.sessions
    let ist0 := CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
    have hload_step : LoadPollStepEnv kit₁ ke₁ st0 z₁.rem.val = LoadPollStepEnv kit₂ ke₂ st0 z₂.rem.val :=
      h3c_seqEnv_congr rfl rfl
    have htrust_step : ∀ k,
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
            ikit₁ ike₁ ist0 z₁.rem.val k .receiving =
          LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
            ikit₂ ike₂ ist0 z₂.rem.val k .receiving :=
      fun _ => h3c_seqEnv_congr rfl (h3c_seqEnv_congr rfl rfl)
    have hsave_step : ∀ k,
        LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
            ikit₁ ike₁ (ikit₁.trustUpdate ist0 z₁.rem.val k .receiving (.ok true)) z₁.rem.val k =
          LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
            ikit₂ ike₂ (ikit₂.trustUpdate ist0 z₂.rem.val k .receiving (.ok true)) z₂.rem.val k :=
      fun _ => h3c_seqEnv_congr rfl (h3c_seqEnv_congr rfl rfl)
    have hstore_call : ∀ rec',
        FromStoreCallEnv kit₁ ke₁ st0 z₁.rem.val rec' = FromStoreCallEnv kit₂ ke₂ st0 z₂.rem.val rec' :=
      fun _ => h3c_seqEnv_congr (h3c_seqEnv_congr rfl (h3c_seqEnv_congr rfl rfl)) rfl
    have htf : FromTrustedFalseEnv z₁ = FromTrustedFalseEnv z₂ :=
      h3c_seqEnv_congr (h3c_stringCloneEnv_eq rfl) rfl
    have htt : ∀ rec' k,
        FromTrustedTrueEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
          FromTrustedTrueEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
      fun rec' k =>
        h3c_seqEnv_congr (hsave_step k)
          (funext fun evs => h3c_or_congr rfl (congrFun (hstore_call rec') evs))
    have hkr : ∀ rec' k,
        FromKeyReadyEnv kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec' k =
          FromKeyReadyEnv kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec' k :=
      fun rec' k =>
        h3c_seqEnv_congr (htrust_step k)
          (funext fun evs =>
            h3c_or_congr rfl (h3c_or_congr (congrFun htf evs) (congrFun (htt rec' k) evs)))
    have hdecRec : ∀ rec,
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
            P.C (pqxdhSpqrModel P) uuidTryParse z₁ rec =
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
            P.C (pqxdhSpqrModel P) uuidTryParse z₂ rec := by
      intro rec
      unfold CryptoVerification.LibsignalPublicApi.MessageDecrypt.decryptRecord
      rfl
    have hps : ∀ rec,
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec =
          FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec :=
      fun rec => funext fun evs =>
        h3c_or_congr rfl
          (h3c_exists_congr fun pt =>
            h3c_exists_congr fun rec' =>
              h3c_exists_congr fun _ =>
                h3c_exists_congr fun k =>
                  h3c_and_congr (congrArg (· = .ok (pt, rec')) (hdecRec rec))
                    (h3c_and_congr rfl
                      (h3c_and_congr rfl (congrFun (hkr rec' k) evs))))
    have hrd : ∀ G ses_st,
        LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv TdEnv
            (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st) =
          LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv TdEnv
            (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st) := by
      intro G ses_st
      funext evs
      unfold LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.RecordDecryptEnv
        LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.FromVEnv
      have htd : ∀ G₁,
          TdEnv (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
              (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st) G₁) =
            TdEnv (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
              (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st) G₁) :=
        fun G₁ => hTd _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl
      have hcond₁ : ((CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st).st.version.toNat =
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₁ 0#64 G ses_st).msg.messageVersion.toNat) =
        (ses_st.version.toNat = m.messageVersion.toNat) := rfl
      have hcond₂ : ((CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st).st.version.toNat =
          (CryptoVerification.LibsignalPublicApi.MessageDecrypt.recGhostOf z₂ 0#64 G ses_st).msg.messageVersion.toNat) =
        (ses_st.version.toNat = m.messageVersion.toNat) := rfl
      by_cases hv : ses_st.version.toNat = m.messageVersion.toNat
      · simp only [hcond₁, hcond₂, hv, ↓reduceIte]
        exact h3c_exists_congr fun G₁ =>
          h3c_and_congr rfl (congrFun (h3c_seqEnv_congr rfl (h3c_seqEnv_congr (htd G₁) rfl)) evs)
      · simp only [hcond₁, hcond₂, hv, ↓reduceIte]
        rfl
    have hrs : ∀ rec G ses_st,
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
            kit₁ ke₁ st0 ikit₁ ike₁ ist0 z₁ rec G ses_st =
          FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
            kit₂ ke₂ st0 ikit₂ ike₂ ist0 z₂ rec G ses_st :=
      fun rec G ses_st => h3c_seqEnv_congr (hrd G ses_st) (hps rec)
    have hlp :
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
            kit₁ ke₁ st0 ikit₁ ike₁ ist0 scopeKit z₁ =
          FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse TdEnv
            kit₂ ke₂ st0 ikit₂ ike₂ ist0 scopeKit z₂ :=
      h3c_seqEnv_congr rfl
        (funext fun evs =>
          h3c_or_congr rfl
            (h3c_or_congr (congrFun htf evs)
              (h3c_or_congr rfl
                (h3c_exists_congr fun rec =>
                  h3c_exists_congr fun ses =>
                    h3c_exists_congr fun G =>
                      h3c_and_congr rfl
                        (h3c_and_congr rfl
                          (h3c_and_congr rfl
                            (congrFun (hrs rec G ses.state) evs)))))))
    funext evs
    exact congrFun (h3c_seqEnv_congr hload_step hlp) evs
  funext evs
  unfold cliDecryptSignalBinaryKitSlotEnvExact
  rw [hF, hp, congrFun hinner evs]

/-- Proves `CliPubCalleesFrozenPlaced` at `ReadFileRuleEnvFixed cliIo.rd`, `binaryKitRunSlotEnvsExact`, `cliDecPkCanonSlotEnvExact`, and `CanonicalOrFallbackPksmEnv PksmTryFromEnv`. -/
theorem hole3_cliPubCallees_canonOrFallback_frozen_ok [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd)) :
    CliPubCalleesFrozenPlaced mmpl gh A lim
      (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      (binaryKitRunSlotEnvsExact W A cliRunBudgets
        (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
      (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
        (binaryKitRunSlotEnvsExact W A cliRunBudgets
          (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
        (CanonicalOrFallbackPksmEnv PksmTryFromEnv))
      W :=
  cliPubCallees_d2c_frozen_ok mmpl gh W hHooks
    (hole3_initEnv_r1c_congr W)
    (hole3_encEnv_r2_congr W A)
    (hole3_decSigEnv_r3a_congr W A)
    hole3_canonOrFallbackPksmEnv_congr
    (fun x y hp hm hs hcp hf hc hmsg => by
      unfold cliDecPkCanonSlotEnvExact
      exact m2rgs3_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'_ghost_congr
        (fun _ K => StatesRecvProtoEnv' K) X W x y hp hm hs hcp hf hc hmsg)

private theorem hole3_runProofs_encDef_eq_agree (P : PEParams)
    (Scope : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)) → Prop) :
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
      rcases CryptoVerification.SignalSession.Cli.Slots.loadRec Scope F peer with _ | (_ | r) <;>
        rfl
    rw [hKey]
    unfold CryptoVerification.SignalSession.Cli.RunProofs.cliAnswers
      CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers
    rcases CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer with _ | _ <;>
      rfl
  funext F peer me ptext coins
  unfold CryptoVerification.SignalSession.Cli.RunProofs.encDef
    CryptoVerification.SignalSession.Cli.RunProofs.Agree.encDef
  rw [hAns F peer]
  generalize CryptoGames.LibsignalSessionApi.messageEncrypt P.C
    CryptoVerification.LibsignalProtoCodec.protoSignalCodec
    (CryptoVerification.E2E.pqxdhSpqrModel P).spqr
    (CryptoVerification.LibsignalPublicApiRepr.serializeAddrVals
      (CryptoVerification.LibsignalTripleRatchetRepr.serviceIdParse uuidTryParse))
    (CryptoVerification.SignalSession.Cli.RunProofs.Agree.cliAnswers Scope F peer
      (CryptoVerification.SignalSession.Cli.RunProofs.Agree.encKey Scope F peer))
    ptext peer me CryptoVerification.SignalSession.Cli.RunCompose.unixEpoch coins = rc
  rcases rc with ⟨err | m, calls⟩
  · cases err <;> rfl
  · dsimp only
    rw [hFinal F calls]

/-! ## Outer Block-579 `run` Composition -/

/-- Composes block-579 `runSpecTightPlaced (LibsignalFrozen lsmpl)` on `mProgPlaced` from `CliGhostAllocHooks`, `CliRunHooksBundle`, and the four inner slot contracts. -/
theorem hole3_hrun_canonOrFallback_of_slots [LibsignalFullPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (_h547 : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim gh)
    (hHooks : CliRunHooksBundle mmpl gh W A lim (ReadFileRuleEnvFixed cliIo.rd))
    (hW1Inner : (mkSlot
      (encSlotSpecPlaced A lim (cliEncryptBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 464))
    (hW2Inner : (mkSlot
      (decSigSlotSpecFrozenPlaced A lim
        (cliDecryptSignalBinaryKitSlotEnvExact W A cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 463))
    (hInit : CliInitSlotOkPlaced mmpl gh A lim (realCliInitBinarySlotEnvFixed W) X W)
    (hDecPk : DecPkD2cSlotOkFrozenPlaced mmpl gh W A lim
      (cliDecPkCanonSlotEnvExact X W)) :
    subroutine_ok (mProgPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 579)
      (runSpecTightPlaced (LibsignalFrozen lsmpl) A lim
        (RunEnv (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets
            (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W))
          (CanonicalOrFallbackPksmEnv PksmTryFromEnv)
          (cliRunSemD2c_placed X W)))
        uuidTryParse
        (runRel (cliRunSemD2c_placed X W))
        cliWrOk cliResStack) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  let S := cliRunSemD2c_placed X W
  let sEnvs := binaryKitRunSlotEnvsExact W A cliRunBudgets
    (realCliInitBinarySlotEnvFixed W) (cliDecPkCanonSlotEnvExact X W)
  let needs := cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)
  have hh := hHooks.runHooks
  have hpub := hole3_cliPubCallees_canonOrFallback_frozen_ok mmpl gh X W hHooks
  have hcallees : RunCalleesPlaced A lim (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
      H cliRunBudgets (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) :=
    { readFile := hHooks.readFile579
      dirGet := hpub.dirGet
      bundleRead := hpub.bundleRead
      splitId := hpub.splitId
      splitSigned := hpub.splitSigned
      dropSpeX := hpub.dropSpeX
      dropSpe := hpub.dropSpe
      encrypt := hW1Inner
      decryptSignal := hW2Inner
      initiate := hInit S sEnvs needs rfl rfl rfl rfl rfl
      decryptPrekey := hDecPk X S needs sEnvs rfl rfl rfl rfl rfl
      kemDeserialize :=
        hc_kemDeserialize_placed (callerProg := lsProg_579 H) (i := 579)
          hh.alloc hh.memcpyRO (by decide) }
  exact
    run_ok_frozen_placed_at_block
      (callerProg := mProgPlaced H) (i := 617)
      (hpub.arms S (cliDecryptPrekeyNeed cliRunBudgets))
      hh
      hcallees
      (hole3_pksmSlotOk_canonOrFallback mmpl gh W hG S rfl)
      (runNeed_cli_le_resStack_placed A lim sEnvs
        (S := S) (decPkNeed := cliDecryptPrekeyNeed cliRunBudgets) (by decide))
      (by decide)
      (by decide)

/-! ## Inner Callee Slot Lemmas (`W1`–`W4`) -/

theorem hole3_w1_inner
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (encSlotSpecPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliEncryptBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).encrypt).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 464) := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W1InnerTightGlue.w1t_hole3_w1_inner_closed
    hLs hblk hext_nodup ghFixed hPl_mng X W γ tp hGSpqr hFs hsat hHooks h547

theorem hole3_w2_inner
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    (mkSlot
      (decSigSlotSpecFrozenPlaced
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        (cliDecryptSignalBinaryKitSlotEnvExact W
          (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliRunBudgets)
        (cliRunSemD2c_placed X W))
      (cliRunNeeds (cliDecryptPrekeyNeed cliRunBudgets)).decryptSignal).OkPlaced
      (lsProg_579 (cliGhostExterns ghFixed (cliExternsPlaced mmpl W))) (mpl.base 463) := by
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W2InnerTight.w2t_hole3_w2_inner
    hLs hblk hext_nodup ghFixed hPl_mng X W γ tp hGSpqr hFs hsat hHooks h547

theorem hole3_w3_init
    {mpl mmpl : MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hblk : ∀ i, i < libsignalSessionLib.blocks.length → (i ∈ libsignalMutatedBlocks) = false →
      (libsignalSessionLib.blockLib i).Placeable (libsignalSessionLib.blockPlacement mpl i))
    (hext_nodup : (libsignalSessionExterns.map mpl.ρ).Nodup)
    (ghFixed : CliGhostHooks)
    (hPl_mng : mallocngLib.Placeable mmpl)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (γ : GhostName) (tp : BitVec 64)
    (hGSpqr :
      letI : LibsignalPlacement := libsignalPlacementOf mpl hblk hext_nodup
      CliGhostSpqrAllocHooks fineCostModel
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits ghFixed)
    (hFs : CliGhostHooksFs ghFixed)
    (hsat : HookSat (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk
        (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
        cliRunBudgets.readFile (ReadFileRuleEnvFixed cliIo.rd)))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns ghFixed (fun _ => none)))
    (hHooks : @CliRunHooksBundle (libsignalPlacementOf mpl hblk hext_nodup) mmpl ghFixed W
      fineCostModel (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (ReadFileRuleEnvFixed cliIo.rd))
    (h547 : mpl.base 547 ≠ 0#64) :
    letI : LibsignalFullPlacement := libsignalFullPlacementOf mpl hLs hblk hext_nodup
    CliInitSlotOkPlaced mmpl ghFixed
      (fineHookRustCliAllocBudget γ mmpl tp cliElfImage.brkStart) cliBudgetLimits
      (realCliInitBinarySlotEnvFixed W) X W := by
  exact w3m_hole3_w3_init hLs hblk hext_nodup ghFixed hPl_mng X W γ tp
    hGSpqr hFs hsat hghNoAlloc hHooks h547

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
