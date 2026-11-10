/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDetPlaced

/-!
# Placed Budgeted CLI `SessionOnlyKitPlacedOkSE` Assembly and Instantiation

Defines ghost-free value-indexed poll allocation envelopes (`SessionStoreBudgetEnv`) for CLI
`SessionFiles`, establishes the lightweight `SessKitHooksPlaced` helper chain, and assembles
budget-threaded `SessionOnlyKitPlacedOkSE` bundles (canonical and `SeqFree`) under
`[LibsignalPlacement]` and `cliExternsPlaced mmpl W`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks
   ls_hook_ok_ultra_of_mem lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.E2E.InMem.SessionStoreImpl (toRecordGhost)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.E2E.Record.Placed (lsProg_46 lsProg_52)
open CryptoVerification.E2E.Record.Serialization (CanonRecord encRecordMem_eq_of_canon)
open CryptoVerification.LibsignalTripleRatchet
  (doReserveStackX extHookStack finishGrowStackX lsMemcpySym)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost protocolAddressAt)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal sessionRecordAt)
open CryptoVerification.LibsignalPublicApi.StoreSession (StorePollCall)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LoadPollCall NoFsEv SessionOnlyVtablesPlacedOk TraceFsSound
   extract_withLsCodeRoLoaded loadPollPlacedOutAtS ls_subroutine_ok_rocl_of_block
   storePollPlacedOutAt subroutine_ok_rocl_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_plain withEnvPre withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsDropOffPlaced_eq lsReadFileSym)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule SessFileWf SessLoadAns addressText cliBcmpName cliBcmpSpec dirAt pathOf
   sessLoadBoxAt sessLoadOutAt sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.KitInst
  (CliSessInv cliIdentityVtRoSym cliSessStoreAt cliSessionKitSpecPlaced cliSessionStoreSpec
   cliSessionStoreSpec_storeUpdate_inv cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
  (addrTextNeedPlaced decNeedPlaced dirPutNeedPlaced growOneDirNeedPlaced
   loadPollNeedPlaced loadShimNeedPlaced storePollNeedXPlaced storeShimNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed
  (blkPl_547 lsProg_542 lsProg_547 lsProg_569 lsProg_570 lsProg_586 lsProg_589
   lsProg_594 lsProg_596 lsProg_597 lsProg_604 lsProg_605)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks CliGhostHooksFs IsFsC allocZeroedHook0_fsT cliGhostExterns
   cliGhostExterns_panic_of_mem hookNoop_fsT traceFsSound_lsProg_cli_ghost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets pathNeed)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced scopeKit)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (CliPanicHooksPlaced satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (canonRecord_of_satisfies_sessionRecordAt)
open CryptoVerification.SpqrV1.Alloc (sessionMemcpyRegionROSpec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
  (BoundedRustEvs SerializeEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec kitStoreShimSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (SessionOnlyKitPlacedOkSE kitLoadPollPlacedSpecS kitLoadPollPlacedSpecSE
   kitStorePollPlacedSpec kitStorePollPlacedSpecE ls_futDrop_ok_of_block)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerializeEnvX serializeCanonSpecX serializeStackX)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudget
  (AddrTextEnv addrText_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.AddressText.PlacedBudgetAux
  (addrDecReserveEvents addrDotReserveEvents addrToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimal_placed_ok_main)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlacedBudget
  (cliFinishGrow_placed_caller_ok_x)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudget
  (dirGet_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.PlacedBudget
  (growOneDirBytes_placed_ok growOneDir_placed_of_bytes)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv path_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget
  (dirPut_placed_caller_ok_of_deps dirPut_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Reserve11PlacedBudget
  (cliDoReserve_placed_ok_at)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunHooksPlaced path_placed_ok reserve_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliAllocHooks CliGhostAllocHooks CliGhostSpqrAllocHooks allocContractsXCliPlaced_of_hooks
   bumpGhost cliExternsPlaced_bcmp_budget_sat cliExternsPlaced_memcpyRegionRO_budget_sat
   cliGhostAllocHooks_bumpGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced ReadFileRuleEnv addrTextSpecPlaced decimalSpecPlaced
   dirGetSpecPlaced dirPutSpecPlaced growOneDirSpecPlaced pathSpecPlaced readFileSpecPlaced
   sessDeserializeSpecPlaced sessLoadPollSpecPlaced sessLoadShimSpecPlaced
   sessStorePollSpecPlaced sessStoreShimSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
  (CliLoadPollEnv OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
  (sessLoadPoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget
  (sessLoadShim_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCliPlacedBudget
  (serializeCanonSeqFree_cli_placed serializeCanonX_cli_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (CliStorePollEnv serializeCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
  (addrText_cells_placed_ok dirPut_cells_placed_ok sessStorePollInner_placed_ok
   sessStorePoll_placed_of_inner)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
  (sessStorePoll_placed_ok_of_depsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
  (sessStoreShim_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open CryptoVerification.E2E.InMem.SessionStoreImpl (record_sessionRecordAt_eq)
open CryptoVerification.E2E.Record.Serialization (SerializeGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (memRegion_32_cells stackAt_sub_split)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid recordGhostValid_of_sessionRecordAt)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SerializeSeqFreeXBudget
  (serializeCanonSeqFreeSpecX)

/-! ## Poll allocation envelopes -/

/-- Value-indexed (`AddrVal`) form of `AddrTextEnv`. -/
def AddrTextValEnv (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (rem : AddrVal) : List AllocEvent → Prop :=
  SeqEnv (· = addrToOwnedEvents rem.name)
    (SeqEnv (· = addrDotReserveEvents rem.name)
      (SeqEnv (DecEnv (rem.device.zeroExtend 32))
        (SeqEnv (· = addrDecReserveEvents rem.name rem.device) FreeOnlyEvs)))

@[simp]
theorem addrTextValEnv_val (DecEnv : BitVec 32 → List AllocEvent → Prop) (g : AddrGhost) :
    AddrTextValEnv DecEnv g.val = AddrTextEnv DecEnv g :=
  rfl

/-- Ghost-independent canonical counterpart of `SerializeEnv` (agrees with `SerializeEnv g r`
under `CanonRecord g r`). -/
def SerializeCanonEnv (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  let encLen := (encodeRecord r).length
  BoundedRustEvs (8 * encLen + 128) (256 * (encLen + 16)) evs

/-- Canonical counterpart of `SerializeEnvX` (`SerializeCanonEnv r` followed by `FreeOnlyEvs`). -/
def SerializeCanonEnvX (r : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv (SerializeCanonEnv r) FreeOnlyEvs

theorem serializeEnv_eq_canon {g : CryptoVerification.E2E.Record.RecordGhost}
    {r : SessionRecord (List (BitVec 8))} (hcanon : CanonRecord g r) :
    SerializeEnv g r = SerializeCanonEnv r := by
  funext evs
  simp only [SerializeEnv, SerializeCanonEnv, encRecordMem_eq_of_canon g r hcanon]

theorem serializeEnvX_eq_canon {g : CryptoVerification.E2E.Record.RecordGhost}
    {r : SessionRecord (List (BitVec 8))} (hcanon : CanonRecord g r) :
    SerializeEnvX g r = SerializeCanonEnvX r := by
  simp only [SerializeEnvX, SerializeCanonEnvX, serializeEnv_eq_canon hcanon]

/-- Value-indexed `load_session` poll envelope for `SessionFiles`: `AddrValEnv`, `Dir::get`,
optional `SessionRecord::deserialize`, and `FreeOnlyEvs` drops. -/
def cliSessionKitLoadPollEnv (rd : ReadRule)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (AddrValEnv : AddrVal → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (F0 : FsFiles) (d : DirGhost) (rem : AddrVal) : List AllocEvent → Prop :=
  SeqEnv (AddrValEnv rem)
    (SeqEnv (GetEnv F0 d (addressText rem))
      (SeqEnv (OptLoadDeserEnv Scope DeserEnv (d.get rd F0 (addressText rem))) FreeOnlyEvs))

/-- Value-indexed `store_session` poll envelope for `SessionFiles`: `AddrValEnv`,
`SessionRecord::serialize`, and `Dir::put`. -/
def cliSessionKitStorePollEnv
    (AddrValEnv : AddrVal → List AllocEvent → Prop)
    (SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (d : DirGhost) (rem : AddrVal) (r : SessionRecord (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (AddrValEnv rem)
    (SeqEnv (SerValEnv r) (PutEnv d (addressText rem) (encodeRecord r)))

def cliSessionKitBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (AddrValEnv : AddrVal → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (vtSym : String := cliSessionVtRoSym)
    (idVtSym : String := cliIdentityVtRoSym) :
    SessionStoreBudgetEnv
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym) where
  loadPollEnv := cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0
  storePollEnv := cliSessionKitStorePollEnv AddrValEnv SerValEnv PutEnv

abbrev cliSessionKitDefaultBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (vtSym : String := cliSessionVtRoSym)
    (idVtSym : String := cliIdentityVtRoSym)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    SessionStoreBudgetEnv
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym) :=
  cliSessionKitBudgetEnv A rd F0 pathOk Scope peer s1 s2 s3 s4
    (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv ReadEnv rd) DeserEnv
    SerializeCanonEnvX DirPutEnv vtSym idVtSym

/-- `SeqFree` `SessionRecord::serialize` envelope
(`∃ g, RecordGhostValid g r ∧ RecordSerializeSeqFreeEnv g r evs`). -/
def SerializeCanonSeqFreeValidEnv (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) :
    Prop :=
  ∃ g : CryptoVerification.LibsignalPublicApiRepr.RecordGhost,
    RecordGhostValid g r ∧ RecordSerializeSeqFreeEnv g r evs

abbrev cliSessionKitSeqFreeBudgetEnv [LibsignalPlacement] (A : RustAlloc)
    (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop)
    (vtSym : String := cliSessionVtRoSym)
    (idVtSym : String := cliIdentityVtRoSym)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop := ReadFileRuleEnv rd) :
    SessionStoreBudgetEnv
      (cliSessionKitSpecPlaced A rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym) :=
  cliSessionKitBudgetEnv A rd F0 pathOk Scope peer s1 s2 s3 s4
    (AddrTextValEnv DecimalEnv) (DirGetEnv PathEnv ReadEnv rd) DeserEnv
    SerializeCanonSeqFreeValidEnv DirPutEnv vtSym idVtSym

/-! ## Shims and `futDrop` -/

section FutDrop
attribute [local irreducible] Program.fetch Program.externAt?

theorem futDropBudget_block_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok (lsProg_547 H) (blkPl_547).base futDropBudgetSpec := by
  dsimp only [lsProg_547, ite_true, futDropBudgetSpec]
  wp_init x s0
  wp_steps
  wp_done

end FutDrop

theorem cliSessFutDrop_rocl_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg (0#64 + lsmpl.base 547) (withLsRoCl lsmpl futDropBudgetSpec) := by
  rw [BitVec.zero_add]
  exact ls_futDrop_ok_of_block (callerProg := callerProg) (j := 547)
    (futDropBudget_block_placed_ok H) hblk (by decide) (by decide)

theorem cliSessLoadShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hC : AllocContractsXCliPlaced A lim H)
    (hs1 : loadShimNeedPlaced ≤ s1)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadShimOff)
      (withLsRoCl lsmpl
        (kitLoadShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym))) := by
  have hcall := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (sessLoadShim_placed_caller_ok_of_deps (callerProg := callerProg) hC hs1 hblk)
  change subroutine_ok callerProg (0#64 + lsmpl.base 604) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hcall (fun _ _ _ hpre => hpre) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  simpa only [withLsRoCl, kitLoadShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec,
    BitVec.zero_add] using hpost

theorem cliSessStoreShim_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    (hC : AllocContractsXCliPlaced A lim H)
    (hs3 : storeShimNeedPlaced ≤ s3)
    (hblk : callerBlk < 619 := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storeShimOff)
      (withLsRoCl lsmpl
        (kitStoreShimSpec M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
            idVtSym))) := by
  have hcall := subroutine_ok_rocl_of_withLsCodeRoLoaded
    (sessStoreShim_placed_caller_ok_of_deps (callerProg := callerProg) hC hs3 hblk)
  change subroutine_ok callerProg (0#64 + lsmpl.base 605) _
  rw [BitVec.zero_add]
  refine subroutine_ok_mono hcall (fun _ _ _ hpre => hpre) ?_ (fun _ _ _ _ hp => hp)
  intro x R s0 sf hpost
  simpa only [withLsRoCl, kitStoreShimSpec, cliSessionKitSpecPlaced, cliSessionStoreSpec,
    BitVec.zero_add] using hpost

/-! ## `SessKitHooksPlaced` and `Dir` helpers -/

/-- Minimal hook/callee bundle for `SessionFiles` (`decimal`, `address_text`, `Dir::get`,
`grow_one`, `Dir::put`). -/
structure SessKitHooksPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : AllocContractsXCliPlaced A lim H
  panics : CliPanicHooksPlaced H
  memcpyRO : HookSat H lsMemcpySym (withVmPreserved sessionMemcpyRegionROSpec)
  bcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec)
  fs : ∀ (prog : Program) (i : Nat), [IsLsBlockProg prog i H] → TraceFsSound prog
  reserve : ∀ {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H] {resStack : Nat},
    doReserveStackX ≤ resStack → i < 619 →
    subroutine_ok callerProg (lsmpl.base 561)
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim))
  path : ∀ {callerProg : Program} {i : Nat} [IsLsBlockProg callerProg i H] {stk : Nat},
    pathNeed ≤ stk → i < 619 →
    subroutine_ok callerProg (lsmpl.base 596) (pathSpecPlaced A lim PathEnv stk)

theorem SessKitHooksPlaced.of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    SessKitHooksPlaced A lim H where
  alloc := hh.alloc
  panics := hh.panics
  memcpyRO := hh.memcpyRO
  bcmp := hh.bcmp
  fs := hh.fs
  reserve := fun hstk hi => reserve_placed_ok hh hstk hi
  path := fun hstk hi => path_placed_ok hh hstk hi

theorem SessKitHooksPlaced.cli [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f) :
    SessKitHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  have halloc := allocContractsXCliPlaced_of_hooks mmpl g W hG
  have hpan : CliPanicHooksPlaced (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    fun _ hmem => cliGhostExterns_panic_of_mem mmpl g W hmem
  have hro := cliExternsPlaced_memcpyRegionRO_budget_sat mmpl g W hG
  have hres : ∀ {callerProg : Program} {i : Nat}
      [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))] {resStack : Nat},
      doReserveStackX ≤ resStack → i < 619 →
      subroutine_ok callerProg (lsmpl.base 561)
        (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)) := by
    intro callerProg i _ resStack hstk hi
    have hrocl := cliDoReserve_placed_ok_at (prog := callerProg) (i := i)
      halloc hstk
      (hpan "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)) hi
    refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_ (fun _ _ _ _ hp => hp)
    intro x R s0 sf hpost
    dsimp only [withLsRoCl, withLsCodeRoLoaded] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  exact
    { alloc := halloc
      panics := hpan
      memcpyRO := hro
      bcmp := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_bcmp_budget_sat mmpl W)
      fs := fun _ _ => traceFsSound_lsProg_cli_ghost mmpl g W
        ⟨hG.alloc_fsT, hG.dealloc_fsT, hG.realloc_fsT, hAzFsT, hG.shim_eq ▸ hookNoop_fsT, hStrFsT,
         by
           obtain ⟨f₀, hf₀, _, _, _, _, _, _, hfsT⟩ := hG.memset
           intro f hf; cases hf₀.symm.trans hf; exact hfsT,
         by
           obtain ⟨f₀, hf₀, _, _, _, _, _, _, _, _, hfsT⟩ := hG.memcpy
           intro f hf; cases hf₀.symm.trans hf; exact hfsT⟩
      reserve := fun hstk hi => hres hstk hi
      path := fun hstk hi =>
        path_placed_caller_ok_of_deps
          (resProg := lsProg_596 (cliGhostExterns g (cliExternsPlaced mmpl W))) (resBlk := 596)
          halloc hro
          (hres (callerProg := lsProg_596 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 596)
            (Nat.le_refl _) (by decide))
          hstk hi (by decide) (by decide) }

theorem SessKitHooksPlaced.cli_of_spqr [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostSpqrAllocHooks M A lim g)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f) :
    SessKitHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  SessKitHooksPlaced.cli mmpl g W hG.toCliGhostAllocHooks hG.allocZeroed_fsT hStrFsT

theorem SessKitHooksPlaced.cli_bumpGhost [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (W : CliHooks) {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliAllocHooks M A lim) :
    SessKitHooksPlaced A lim (cliGhostExterns bumpGhost (cliExternsPlaced mmpl W)) :=
  SessKitHooksPlaced.cli mmpl bumpGhost W (cliGhostAllocHooks_bumpGhost hA)
    allocZeroedHook0_fsT (fun _ h => by cases h)

theorem cliDecimal_placed_ok_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : SessKitHooksPlaced A lim H) :
    subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecimalEnv decNeedPlaced) :=
  decimal_placed_ok_main
    (hh.reserve (callerProg := lsProg_597 H) (i := 597)
      (Nat.le_refl doReserveStackX) (by decide))
    (Nat.le_refl decNeedPlaced)

theorem cliDecimal_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (lsProg_597 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecimalEnv decNeedPlaced) :=
  cliDecimal_placed_ok_of_sessHooks (SessKitHooksPlaced.of_runHooks hh)

theorem cliAddrText_placed_ok_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : SessKitHooksPlaced A lim H) :
    subroutine_ok (lsProg_594 H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim (AddrTextEnv DecimalEnv) addrTextNeedPlaced) :=
  addrText_placed_ok_of_deps
    (resProg := lsProg_594 H) (decProg := lsProg_597 H) (resBlk := 594) (decBlk := 597)
    hh.alloc
    (hh.reserve (callerProg := lsProg_594 H) (i := 594)
      (Nat.le_refl doReserveStackX) (by decide))
    (cliDecimal_placed_ok_of_sessHooks hh)
    (Nat.le_refl addrTextNeedPlaced)
    (by decide) (by decide) (by decide) (by decide)

theorem cliAddrText_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (lsProg_594 H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim (AddrTextEnv DecimalEnv) addrTextNeedPlaced) :=
  cliAddrText_placed_ok_of_sessHooks (SessKitHooksPlaced.of_runHooks hh)

theorem cliDirGet_placed_ok_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)) :=
  dirGet_placed_ok_of_deps hpathLen hh.alloc hh.memcpyRO hh.bcmp
    (jPath := 589) (by decide) (by decide)
    (hh.path (callerProg := lsProg_589 H) (i := 589) (Nat.le_refl pathNeed) (by decide))
    hjRead hjRead_unmut hRead (hh.fs (lsProg_589 H) 589)
    (Nat.le_refl (RunBudgets.dirGetNeed ⟨readStk⟩))
    (fun _ _ _ _ h => h)

theorem cliDirGet_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (DirGetEnv PathEnv ReadEnv rd)
        (RunBudgets.dirGetNeed ⟨readStk⟩)) :=
  cliDirGet_placed_ok_of_sessHooks hpathLen (SessKitHooksPlaced.of_runHooks hh)
    hRead hjRead hjRead_unmut

theorem cliGrowOneDir_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (hpan : CliPanicHooksPlaced H) :
    subroutine_ok (lsProg_586 H) (lsmpl.base 586)
      (growOneDirSpecPlaced A lim growOneDirNeedPlaced) :=
  growOneDir_placed_of_bytes
    (growOneDirBytes_placed_ok hpan
      (cliFinishGrow_placed_caller_ok_x (callerProg := lsProg_586 H) (i := 586)
        hC (by decide)))
    (Nat.le_refl growOneDirNeedPlaced)

theorem cliDirPut_placed_ok_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : SessKitHooksPlaced A lim H) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim DirPutEnv dirPutNeedPlaced) :=
  dirPut_placed_caller_ok_of_deps (callerProg := lsProg_570 H) (i := 570)
    hh.alloc hh.bcmp (growProg := lsProg_586 H) (jGrow := 586) (by decide) (by decide)
    (cliGrowOneDir_placed_ok hh.alloc hh.panics) (Nat.le_refl dirPutNeedPlaced) (by decide)

theorem cliDirPut_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hh : RunHooksPlaced A lim H) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim DirPutEnv dirPutNeedPlaced) :=
  cliDirPut_placed_ok_of_sessHooks (SessKitHooksPlaced.of_runHooks hh)

/-! ## `sessLoadPoll` and `sessStorePoll` -/

theorem cliSessLoadPoll_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {SerValEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg getProg deserProg : Program}
    {callerBlk addrBlk getBlk deserBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg deserProg deserBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim (fun g => AddrValEnv g.val) addrTextNeedPlaced))
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv (RunBudgets.dirGetNeed ⟨readStk⟩)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hFs : TraceFsSound (lsProg_569 H))
    (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).loadPollOff)
      (withLsRoCl lsmpl
        (kitLoadPollPlacedSpecSE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym)
          Scope encodeRecord)) := by
  have h569 := sessLoadPoll_placed_ok_of_deps hC hAddr hGet hDeser hFs hs2
    hAddrBlk hAddrUnmut hGetBlk hGetUnmut hDeserBlk hDeserUnmut
  have h569_kit : subroutine_ok (lsProg_569 H) (lsmpl.base 569)
      (withLsCodeRoLoaded lsmpl
        (kitLoadPollPlacedSpecSE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerValEnv PutEnv vtSym idVtSym)
          Scope encodeRecord)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d call.addr.val)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A.repAlloc self d ∗
          memRegion call.out 368 ∗ protocolAddressAt A.repAlloc call.addr call.addrA ∗
          A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hname : call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hfit_hop : FitsEnv M lim st
        (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
          s0.fs.files ⟨call, self, d⟩) := by
      rw [hfiles]
      exact hfit
    have hhop_pure :
        s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          call.addr.name.bytes.length < 2 ^ 32 ∧
          (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
          pathOk (pathOf d.path (addressText call.addr.val)) ∧
          (∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs → SessFileWf Scope bs) ∧
          FitsEnv M lim st
            (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
              s0.fs.files ⟨call, self, d⟩) :=
      ⟨hx0, hx8, hname ▸ hinv.nameLt, haddr ▸ hinv.textLt, hinv.pathLt, haddr ▸ hinv.pathOk,
        fun bs hbs => by
          rw [hfiles, haddr] at hbs
          obtain ⟨bs₀, hget₀, hwf₀⟩ := hinv.getOk
          rw [hget₀] at hbs
          cases hbs
          exact hwf₀,
        hfit_hop⟩
    have hm_hop : s0.mem ⊨
        (sessLoadPollSpecPlaced rd pathOk Scope A lim
          (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv) s2).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.addr.name.bytes.length < 2 ^ 32 ∧
            (addressText call.addr.val).length < 2 ^ 32 ∧ d.path.length < 2 ^ 32 ∧
            pathOk (pathOf d.path (addressText call.addr.val)) ∧
            (∀ bs, d.get rd s0.fs.files (addressText call.addr.val) = .ok bs →
              SessFileWf Scope bs) ∧
            FitsEnv M lim st
              (CliLoadPollEnv rd Scope (fun g => AddrValEnv g.val) GetEnv DeserEnv
                s0.fs.files ⟨call, self, d⟩)⌝ ∗
          (sessLoadBoxAt call.fut self call.addrA 0#8 ∗ dirAt A.repAlloc self d ∗
            memRegion call.out 368 ∗ protocolAddressAt A.repAlloc call.addr call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s2 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨hhop_pure, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h569.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, gr, ans, ⟨⟨hgr, htr⟩, hans, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d call.addr.val evs := by
        rw [hfiles] at hevs
        exact hevs
      rw [hfiles, haddr] at hgr
      obtain ⟨bs₀, hget₀, _⟩ := hinv.getOk
      rw [hget₀] at hgr
      subst hgr
      have hout_ent : sessLoadOutAt A.repAlloc call.out ans ⊢
          loadPollPlacedOutAtS Scope A.repAlloc call.out ans := by
        cases bs₀ with
        | nil =>
          have hans' : ans = .ok none := hans
          subst hans'
          exact Entails.refl _
        | cons b bs =>
          obtain ⟨r, hans', _, hsc⟩ := hans
          subst hans'
          exact Entails.pure_right hsc (Entails.refl _)
      have hm_out : sf.mem ⊨
          loadPollPlacedOutAtS Scope A.repAlloc call.out ans ∗
            (sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A.repAlloc self d ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R) :=
        Satisfies.mono (sepConj_mono_left hout_ent) hm
      dsimp only [withLsCodeRoLoaded, kitLoadPollPlacedSpecSE, withEnvPre, kitLoadPollPlacedSpecS,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨ans, evs, ?_⟩
      have hgoal : sf.mem ⊨
          ⌜(∃ bs, d.get rd F0 (addressText call.addr.val) = .ok bs ∧
              SessLoadAns Scope (.ok bs) ans) ∧
            sf.trace = s0.trace ++ [] ∧
            cliSessionKitLoadPollEnv rd Scope AddrValEnv GetEnv DeserEnv F0 d
              call.addr.val evs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
            (loadPollPlacedOutAtS Scope A.repAlloc call.out ans ∗
              sessLoadBoxAt call.fut self call.addrA 1#8 ∗ dirAt A.repAlloc self d ∗
              protocolAddressAt A.repAlloc call.addr call.addrA ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s2 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨⟨bs₀, haddr.symm ▸ hget₀, hans⟩, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv, hm_out⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessLoadPollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 569) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 569)
    h569_kit hCallerBlk (by decide) (by decide)

theorem cliSessStorePoll_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg serProg putProg : Program}
    {callerBlk addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim (fun g => AddrValEnv g.val) addrTextNeedPlaced))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv dirPutNeedPlaced))
    (hs4 : storePollNeedXPlaced ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonEnvX PutEnv vtSym idVtSym)
          encodeRecord)) := by
  have h570 := sessStorePoll_placed_ok_of_depsX hC hAddr hSer hPut hs4
    hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonEnvX PutEnv vtSym idVtSym)
          encodeRecord)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
              d call.call.addr.val call.call.record)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
          sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hspatial
    have hcanon : CanonRecord (toRecordGhost call.call.g) call.call.record :=
      canonRecord_of_satisfies_sessionRecordAt A.repAlloc call.call.recA
        call.call.g call.call.record _ s0.mem hrec_sat
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv ⟨call, self, d⟩) := by
      simpa only [CliStorePollEnv, cliSessionKitStorePollEnv, serializeEnvX_eq_canon hcanon]
        using hfit
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv) s4).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv (fun g => AddrValEnv g.val) SerializeEnvX PutEnv
                ⟨call, self, d⟩)⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
            d call.call.addr.val call.call.record evs := by
        simpa only [CliStorePollEnv, cliSessionKitStorePollEnv, serializeEnvX_eq_canon hcanon]
          using hevs
      have hinv' : CliSessInv rd F0 pathOk Scope peer
          (d.put (addressText call.call.addr.val) (encodeRecord call.call.record)) :=
        cliSessionStoreSpec_storeUpdate_inv (A := A.repAlloc) (b := 0#64)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
      dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
            cliSessionKitStorePollEnv AddrValEnv SerializeCanonEnvX PutEnv
              d call.call.addr.val call.call.record evs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer
              (d.put (addressText call.call.addr.val) (encodeRecord call.call.record))⌝ ∗
            (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
              dirAt A.repAlloc self (d.put (addressText call.call.addr.val)
                (encodeRecord call.call.record)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
              sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

/-! ## `SessionOnlyKitPlacedOkSE` bundles and CLI specializations -/

abbrev SessionOnlyKitPlacedRoClOkSE [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : CryptoVerification.LibsignalPublicApi.StoreKit.SessionStoreSpec A.repAlloc 0#64)
    (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H

/-- Assemble `SessionOnlyKitPlacedOkSE` for `cliSessionKitSpecPlaced` from `SessKitHooksPlaced`. -/
theorem cliSessKitOkSE_placed_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H := by
  have hAddr := cliAddrText_placed_ok_of_sessHooks hh
  have hGet := cliDirGet_placed_ok_of_sessHooks hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPut_placed_ok_of_sessHooks hh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
        (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_placed_ok hh.alloc hAddr hSer hPut hs4 hblk
        (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

/-- Assemble `SessionOnlyKitPlacedOkSE` for `cliSessionKitSpecPlaced` from `RunHooksPlaced`. -/
theorem cliSessKitOkSE_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  cliSessKitOkSE_placed_of_sessHooks hDropNz hpathLen (SessKitHooksPlaced.of_runHooks hh)
    hRead hDeser hSer hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut hSerBlk hSerUnmut

theorem cliSessKitRoClOkSE_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  cliSessKitOkSE_placed hDropNz hpathLen hh hRead hDeser hSer hs1 hs2 hs3 hs4
    hjRead hjRead_unmut hDeserBlk hDeserUnmut hSerBlk hSerUnmut

theorem cliSessionVtablesCli_placed [LibsignalPlacement] {A : RustAlloc} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {idVtSym : String} (hDropNz : lsmpl.base 547 ≠ 0#64) :
    SessionOnlyVtablesPlacedOk
      (cliSessionKitSpecPlaced A cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        cliSessionVtRoSym idVtSym) :=
  CryptoVerification.SignalSession.Cli.KitInst.cliSessionKitSpecPlaced_vtables hDropNz

/-- Budget-threaded `SessionOnlyKitPlacedOkSE` at
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliSessKitOkSE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_placed_of_sessHooks
    (serProg := lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) (SessKitHooksPlaced.cli mmpl g W hG hAzFsT hStrFsT)
    hRead hDeser (serializeCanonX_cli_placed mmpl g W hG)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut (by decide) (by decide)

theorem cliSessKitRoClOkSE_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hDeser hs1 hs2 hs3 hs4
    hjRead hjRead_unmut hDeserBlk hDeserUnmut

theorem cliSessKitOkSE_cli_placed_of_readHook [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {deserProg : Program} {deserBlk : Nat}
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed mmpl g W
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz hG hAzFsT hStrFsT
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    hDeser hs1 hs2 hs3 hs4 (by decide) (by decide) hDeserBlk hDeserUnmut

theorem sessDeserialize_of_sub_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (hDeser : subroutine_ok prog entry (sessDeserializeSpecPlaced Scope' A lim DeserEnv))
    (hsub : ∀ r, Scope r → Scope' r) :
    subroutine_ok prog entry (sessDeserializeSpecPlaced Scope A lim DeserEnv) := by
  refine subroutine_ok_mono hDeser (fun ⟨x, st⟩ R s0 hpre => ?_)
    (fun _ _ _ _ hpost => hpost) (fun _ _ _ _ hp => hp)
  obtain ⟨hcrl, hrest⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hrest
  rw [sepConj_assoc, satisfies_pure_sepConj] at hrest
  obtain ⟨⟨hx0, hx1, hx8, hsc, hfit⟩, hmem⟩ := hrest
  refine satisfies_lscro_pre hcrl ?_
  dsimp only
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0, hx1, hx8, hsub x.r hsc, hfit⟩, hmem⟩

theorem cliSessKitOkSE_cli_scopeKit_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeserScopeKit : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead
    (sessDeserialize_of_sub_placed_ok hDeserScopeKit hsub)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut

theorem cliSessKitRoClOkSE_cli_scopeKit_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeserScopeKit : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitDefaultBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_cli_scopeKit_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead hDeserScopeKit hsub
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut

/-! ## `SeqFree` `SessionOnlyKitPlacedOkSE` lift -/

private theorem seqEnv_mono {P₁ P₂ Q₁ Q₂ : List AllocEvent → Prop}
    (hP : ∀ e, P₁ e → P₂ e) (hQ : ∀ e, Q₁ e → Q₂ e)
    {evs : List AllocEvent} (h : SeqEnv P₁ Q₁ evs) :
    SeqEnv P₂ Q₂ evs := by
  rcases h with hp | ⟨e₁, e₂, rfl, hp, hq⟩
  · exact Or.inl (hP evs hp)
  · exact Or.inr ⟨e₁, e₂, rfl, hP e₁ hp, hQ e₂ hq⟩

abbrev RecordSerializeSeqFreeCellsEnv
    (g : CryptoVerification.E2E.Record.RecordGhost)
    (r : SessionRecord (List (BitVec 8))) : List AllocEvent → Prop :=
  RecordSerializeSeqFreeEnv ⟨g.prevCap, g.prevPtr, g.cur⟩ r

theorem serialize_cells_seqFree_placed_okX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hle : serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        (serializeCellsSpec A lim RecordSerializeSeqFreeCellsEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  have hrec_eq :
      CryptoVerification.E2E.Record.sessionRecordAt A.repAlloc recA g r =
        sessionRecordAt A.repAlloc recA ⟨g.prevCap, g.prevPtr, g.cur⟩ r := by
    cases g; rfl
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : SerializeGhost × M.σ := (⟨recA, out, g, r⟩, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)).pre callG s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializeCanonSeqFreeSpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen, ?_⟩, ?_⟩
    · cases g; exact hfit
    · dsimp only [stkRem]
      rw [hrec_eq] at hmem
      cases g
      convert hmem using 1; sep_ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX, serializeCellsSpec, callG] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨evs, bCap, bPtr, ?_⟩
    rw [vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, by cases g; exact hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi, hrec_eq]
    dsimp only [okTagVec, stkRem] at hq
    cases g
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSeqFreeSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePoll_seqFree_placed_ok_of_depsX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (_hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStackX) (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim
        (CliStorePollEnv AddrEnv RecordSerializeSeqFreeCellsEnv PutEnv) stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_cl_to_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_seqFree_placed_okX hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

theorem cliSessStorePoll_rocl_seqFree_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {AddrValEnv : AddrVal → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {callerProg addrProg serProg putProg : Program}
    {callerBlk addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim (fun g => AddrValEnv g.val) addrTextNeedPlaced))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv dirPutNeedPlaced))
    (hs4 : storePollNeedXPlaced ≤ s4)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg
      (0#64 + (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym
        idVtSym).storePollOff)
      (withLsRoCl lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord)) := by
  have h570 := sessStorePoll_seqFree_placed_ok_of_depsX hC hAddr hSerSeqFree hPut hs4
    hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut
  have h570_kit : subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (kitStorePollPlacedSpecE M A lim
          (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
          (cliSessionKitBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
            AddrValEnv GetEnv DeserEnv SerializeCanonSeqFreeValidEnv PutEnv vtSym idVtSym)
          encodeRecord)) := by
    refine subroutine_ok_outcome_intro fun ⟨call, self, d, st⟩ R s0 hpc hrun hpre hsp => ?_
    obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre
    dsimp only [kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
      cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt] at hpre0
    have hpre' : s0.mem ⊨
        ⌜s0.fs.files = F0⌝ ∗
        (⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
          (Scope call.call.record ∧ (encodeRecord call.call.record).length < 2 ^ 32) ∧
          call.call.addr.val = peer.val ∧
          FitsEnv M lim st
            (cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
              d call.call.addr.val call.call.record)⌝ ∗
        (⌜CliSessInv rd F0 pathOk Scope peer d⌝ ∗
        (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
          dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
          protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
          sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R))) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre0
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨_hfiles, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx8, hrec, haddr, hfit⟩, hpre'⟩ := hpre'
    rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hinv, hspatial⟩ := hpre'
    have hrec_sat : s0.mem ⊨
        sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hspatial
    have hgvalid : RecordGhostValid call.call.g call.call.record :=
      recordGhostValid_of_sessionRecordAt hrec_sat
    have hcells_eq : ∀ evs,
        RecordSerializeSeqFreeCellsEnv (toRecordGhost call.call.g) call.call.record evs =
          RecordSerializeSeqFreeEnv call.call.g call.call.record evs := by
      intro evs; cases call.call.g; rfl
    have hfit_hop : FitsEnv M lim st
        (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv
          ⟨call, self, d⟩) := by
      intro evs he
      exact hfit evs
        (seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono
              (fun e hs => ⟨call.call.g, hgvalid, (hcells_eq e).mp hs⟩)
              (fun _ hp => hp) h2)
          he)
    have hname : call.call.addr.name.bytes = peer.name.bytes := congrArg AddrVal.name haddr
    have hm_hop : s0.mem ⊨
        (sessStorePollSpecPlaced A lim
          (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv) s4).pre
          (⟨call, self, d⟩, st) s0 ∗ R := by
      refine satisfies_lscro_pre hcrl ?_
      dsimp only
      have h1 : s0.mem ⊨
          ⌜s0.readReg64 .x0 = call.fut ∧ s0.readReg64 .x8 = call.out ∧
            call.call.addr.name.bytes.length < 2 ^ 32 ∧
            (encodeRecord call.call.record).length < 2 ^ 32 ∧
            d.changed.length < 2 ^ 32 ∧
            FitsEnv M lim st
              (CliStorePollEnv (fun g => AddrValEnv g.val) RecordSerializeSeqFreeCellsEnv PutEnv
                ⟨call, self, d⟩)⌝ ∗
          (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 0#8 ∗
            dirAt A.repAlloc self d ∗ memRegion call.out 48 ∗
            protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
            sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
            A.pool lim st s0 ∗ stackAt s0.sp s4 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨hx0, hx8, hname ▸ hinv.nameLt, hrec.2, hinv.changedLt.1, hfit_hop⟩, hspatial⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) h1
    refine h570.mono_outcome (⟨call, self, d⟩, st) R s0 hpc hrun hm_hop hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hpost
      simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
        satisfies_pure_sepConj] at hpost
      obtain ⟨evs, ⟨htr, hevs⟩, hm⟩ := hpost
      have hevs_kit :
          cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
            d call.call.addr.val call.call.record evs :=
        seqEnv_mono (fun _ ha => ha)
          (fun _ h2 =>
            seqEnv_mono
              (fun e hs => ⟨call.call.g, hgvalid, (hcells_eq e).mp hs⟩)
              (fun _ hp => hp) h2)
          hevs
      have hinv' : CliSessInv rd F0 pathOk Scope peer
          (d.put (addressText call.call.addr.val) (encodeRecord call.call.record)) :=
        cliSessionStoreSpec_storeUpdate_inv (A := A.repAlloc) (b := 0#64)
          (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (ans := .ok ()) hinv haddr hrec
      dsimp only [withLsCodeRoLoaded, kitStorePollPlacedSpecE, withEnvPre, kitStorePollPlacedSpec,
        cliSessionKitSpecPlaced, cliSessionKitBudgetEnv, cliSessionStoreSpec, cliSessStoreAt]
      simp only [sepExists_sepConj_left, satisfies_sepExists]
      refine ⟨.ok (), evs, ?_⟩
      dsimp only [storePollPlacedOutAt]
      have hgoal : sf.mem ⊨
          ⌜(Except.ok () : Except Unit Unit) = .ok () ∧ sf.trace = s0.trace ++ [] ∧
            cliSessionKitStorePollEnv AddrValEnv SerializeCanonSeqFreeValidEnv PutEnv
              d call.call.addr.val call.call.record evs⌝ ∗
          (⌜CliSessInv rd F0 pathOk Scope peer
              (d.put (addressText call.call.addr.val) (encodeRecord call.call.record))⌝ ∗
            (sessStoreBoxAt call.fut self call.call.addrA call.call.recA 1#8 ∗
              dirAt A.repAlloc self (d.put (addressText call.call.addr.val)
                (encodeRecord call.call.record)) ∗
              (call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (call.out + 8#64) 40 ∗
              protocolAddressAt A.repAlloc call.call.addr call.call.addrA ∗
              sessionRecordAt A.repAlloc call.call.recA call.call.g call.call.record ∗
              A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp s4 ∗ R)) := by
        rw [satisfies_pure_sepConj]
        refine ⟨⟨rfl, by rw [List.append_nil]; exact htr, hevs_kit⟩, ?_⟩
        rw [satisfies_pure_sepConj]
        exact ⟨hinv', Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hm⟩
      exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hgoal
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
    · dsimp only [sessStorePollSpecPlaced, withLsCodeRoLoaded] at hq
      exact (not_satisfies_false_sepConj hq).elim
  change subroutine_ok callerProg (0#64 + lsmpl.base 570) _
  rw [BitVec.zero_add]
  exact ls_subroutine_ok_rocl_of_block (callerProg := callerProg) (j := 570)
    h570_kit hCallerBlk (by decide) (by decide)

theorem cliSessKitOkSE_seqFree_placed_of_sessHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : SessKitHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H := by
  have hAddr := cliAddrText_placed_ok_of_sessHooks hh
  have hGet := cliDirGet_placed_ok_of_sessHooks hpathLen hh hRead hjRead hjRead_unmut
  have hPut := cliDirPut_placed_ok_of_sessHooks hh
  exact
    { loadShim := fun hblk => cliSessLoadShim_rocl_placed_ok hh.alloc hs1 hblk
      loadPoll := fun hblk => cliSessLoadPoll_rocl_placed_ok hh.alloc hAddr hGet hDeser
        (hh.fs (lsProg_569 H) 569) hs2 hblk (by decide) (by decide) (by decide) (by decide)
        hDeserBlk hDeserUnmut
      loadFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk
      storeShim := fun hblk => cliSessStoreShim_rocl_placed_ok hh.alloc hs3 hblk
      storePoll := fun hblk => cliSessStorePoll_rocl_seqFree_placed_ok hh.alloc hAddr hSerSeqFree
        hPut hs4 hblk (by decide) (by decide) hSerBlk hSerUnmut (by decide) (by decide)
      storeFutDrop := fun hblk => by
        dsimp only [cliSessionKitSpecPlaced]
        rw [lsDropOffPlaced_eq hDropNz]
        exact cliSessFutDrop_rocl_placed_ok hblk }

theorem cliSessKitOkSE_seqFree_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg serProg : Program} {jRead deserBlk serBlk : Nat}
    [IsLsBlockProg readProg jRead H]
    [IsLsBlockProg deserProg deserBlk H]
    [IsLsBlockProg serProg serBlk H]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hh : RunHooksPlaced A lim H)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hSerSeqFree : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSeqFreeSpecX M A lim)))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4 vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc rd F0 pathOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord H :=
  cliSessKitOkSE_seqFree_placed_of_sessHooks hDropNz hpathLen (SessKitHooksPlaced.of_runHooks hh)
    hRead hDeser hSerSeqFree hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut
    hSerBlk hSerUnmut

theorem cliSessKitOkSE_seqFree_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement)
    (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_placed_of_sessHooks
    (serProg := lsProg_52 (cliGhostExterns g (cliExternsPlaced mmpl W))) (serBlk := 52)
    hDropNz (fun _ hp => hp.2) (SessKitHooksPlaced.cli mmpl g W hG hAzFsT hStrFsT)
    hRead hDeser (serializeCanonSeqFree_cli_placed mmpl g W hG)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut (by decide) (by decide)

theorem cliSessKitOkSE_seqFree_cli_placed_of_readHook [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {deserProg : Program} {deserBlk : Nat}
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hReadHook : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv))
    (hDeser : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced Scope A lim DeserEnv))
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_cli_placed mmpl g W
    (readProg := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz hG hAzFsT hStrFsT
    (subroutine_ok_withLsCodeRoLoaded_of_plain
      (ls_hook_ok_ultra_of_mem
        (prog := lsProg_589 (cliGhostExterns g (cliExternsPlaced mmpl W))) (i := 589)
        hReadHook (by decide) (by decide) (by decide)))
    hDeser hs1 hs2 hs3 hs4 (by decide) (by decide) hDeserBlk hDeserUnmut

theorem cliSessKitOkSE_seqFree_cli_scopeKit_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeserScopeKit : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_cli_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead
    (sessDeserialize_of_sub_placed_ok hDeserScopeKit hsub)
    hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut

theorem cliSessKitRoClOkSE_seqFree_cli_scopeKit_placed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F0 : FsFiles}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {peer : AddrGhost}
    {DeserEnv : SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {readStk s1 s2 s3 s4 : Nat} {vtSym idVtSym : String}
    {readProg deserProg : Program} {jRead deserBlk : Nat}
    [IsLsBlockProg readProg jRead (cliGhostExterns g (cliExternsPlaced mmpl W))]
    [IsLsBlockProg deserProg deserBlk (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : CliGhostAllocHooks M A lim g)
    (hAzFsT : HookFsTraced IsFsC g.allocZeroed)
    (hStrFsT : ∀ f, g.stringClone = some f → HookFsTraced IsFsC f)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl (readFileSpecPlaced cliIo.rd cliWrOk A lim readStk ReadEnv)))
    (hDeserScopeKit : subroutine_ok deserProg (lsmpl.base 46)
      (sessDeserializeSpecPlaced scopeKit A lim DeserEnv))
    (hsub : ∀ r, Scope r → scopeKit r)
    (hs1 : loadShimNeedPlaced ≤ s1) (hs2 : loadPollNeedPlaced readStk ≤ s2)
    (hs3 : storeShimNeedPlaced ≤ s3) (hs4 : storePollNeedXPlaced ≤ s4)
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hDeserBlk : deserBlk < 619 := by decide)
    (hDeserUnmut : (deserBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    SessionOnlyKitPlacedRoClOkSE A lim
      (cliSessionKitSpecPlaced A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        vtSym idVtSym)
      (cliSessionKitSeqFreeBudgetEnv A.repAlloc cliIo.rd F0 cliWrOk Scope peer s1 s2 s3 s4
        DeserEnv vtSym idVtSym ReadEnv)
      Scope encodeRecord (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliSessKitOkSE_seqFree_cli_scopeKit_placed mmpl g W hDropNz hG hAzFsT hStrFsT hRead
    hDeserScopeKit hsub hs1 hs2 hs3 hs4 hjRead hjRead_unmut hDeserBlk hDeserUnmut

end LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
