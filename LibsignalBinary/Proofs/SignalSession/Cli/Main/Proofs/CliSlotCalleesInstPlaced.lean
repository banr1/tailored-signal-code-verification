/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.InnerInstPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.InnerInstPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVTPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpecPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.FinishGrowPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.UuidFsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.ParseSidFsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
public import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
public import LibsignalBinary.Proofs.TripleRatchet.Wire.New
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarint
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
public import LibsignalBinary.Proofs.TripleRatchet.Mac.Compute
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls

/-!
# Relocatable `CliSlotCalleesPlaced` Assembly

Assembles the encrypt (`w1_inner_placed_ok`), decrypt (`w2_inner_placed_ok_of_region`,
`w2_inner_placed_ok`), and session-initiation (`w3*`) callee contracts into
`CliSlotCalleesPlaced` and `CliSlotCalleesFullPlaced` under `[LibsignalPlacement]`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

private theorem spqrV1_eq_spqrV1W (W : CliHooks) :
    CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K = pqxdhSpqrModel ⟨W.C, W.Q⟩ :=
  rfl

private theorem cliGhostExterns_row_eq (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) {sym : String} {f : State → State}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some f :=
  (RunGlue.cliGhostExterns_other gh _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans
    (RunGlue.cliExternsPlaced_row mmpl W hrow)

/-! ## Placed Store Kits and Vtable Witnesses -/

private theorem w1SessKitPlaced_eq_cliSessionKitSpecPlaced [LibsignalPlacement]
    (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost) :
    EncryptLemmas.w1SessKitPlaced B F0 peer =
      SessKit.cliSessionKitSpecPlaced E2E.HooksE.A0 cliIo.rd F0 cliWrOk Slots.scopeKit peer
        SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
        SessKit.storeShimNeed SessKit.storePollNeedX
        cliSessionVtRoSym cliIdentityVtRoSym :=
  rfl

theorem w2SessVt_placed_ok [LibsignalPlacement] (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyVtablesPlacedOk (DecryptLemmas.decSessKitPlaced F0 peer B) := by
  dsimp only [DecryptLemmas.decSessKitPlaced]
  rw [w1SessKitPlaced_eq_cliSessionKitSpecPlaced]
  exact SessKit.cliSessionVtablesCli_placed hDropNz

theorem w2IdVt_placed_ok [LibsignalPlacement] (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (F0 : FsFiles) (peer : AddrGhost) :
    IdentityVtablesPlacedOk (DecryptLemmas.decIdKitPlaced F0 peer B) := by
  refine cliIdentityVtablesPlacedOk ?_
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    lsDropOffPlaced_eq hDropNz, lsDropOffPlaced_eq hDropNz, rfl, rfl⟩

theorem w1SessKitPlaced_okSE [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (B : RunBudgets)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym) (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 B.readFile))
    (F0 : FsFiles) (peer : AddrGhost) :
    SessionOnlyKitPlacedOkSE (EncryptLemmas.w1SessKitPlaced B F0 peer)
      Slots.scopeKit E2E.Record.encodeRecord (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  rw [w1SessKitPlaced_eq_cliSessionKitSpecPlaced]
  exact SessKit.cliSessKitOkSE_cli_scopeKit_placed mmpl gh W (readStk := B.readFile)
    (readProg := Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
    hDropNz hh hRead (KitInst.stage2ContractsMinPlaced_of_runHooks mmpl gh W hh)
    (fun _ h => h) (by decide) (Nat.le_refl _) (by decide) (by decide)

abbrev cliDirPutStrNeedPlaced : Nat :=
  0x50 + max (0x40 + CryptoVerification.LibsignalTripleRatchet.finishGrowStackX) extHookStack

/-- Block-`543` `Dir::put::<&str>` contract obligation. -/
def DirPutStrPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  subroutine_ok (Placed.lsProg_543 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 543)
    (dirPutStrSpecPlaced E2E.HooksE.A0 cliDirPutStrNeedPlaced)

theorem dirPutStrPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    DirPutStrPlacedOk mmpl gh W :=
  PutStr.dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
    (growProg := Placed.lsProg_586 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jGrow := 586)
    (by decide) (by decide) (SessKit.cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl cliDirPutStrNeedPlaced)

/-! ## Inner Decrypt (`w2_inner_placed_ok_of_region`) -/

private theorem cliExternsPlaced_blackBox_eq
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook :=
  cliGhostExterns_row_eq mmpl gh W (Slots.blackBox_row_placed mmpl W)

/-- Proves `InnerDecryptPlacedOk` on Block `463` from `hDropNz` and the Block-`463` `region_ok`
hypothesis `hreg`. -/
theorem w2_inner_placed_ok_of_region [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hreg : region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTight
        W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)).withVRegs.restrictPre
        ((fun _ => True) ·.st.pqRatchetState))) :
    DecryptLemmas.InnerDecryptPlacedOk mmpl gh W cliRunBudgets_placed :=
  DecryptLemmas.w2_inner_placed_ok_of_region mmpl gh W (B := cliRunBudgets_placed)
    hDropNz hG hh hRead589 hreg

/-- `withLsFrozen` variant proving `InnerDecryptFrozenPlacedOk` from `hDropNz` and `hreg`. -/
theorem w2_inner_frozen_placed_ok_of_region [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hreg : region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((withLsFrozen lsmpl
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTight
          W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))).withVRegs.restrictPre
        (fun _ => True))) :
    DecryptLemmas.InnerDecryptFrozenPlacedOk mmpl gh W cliRunBudgets_placed :=
  DecryptLemmas.w2_inner_frozen_placed_ok_of_region mmpl gh W (B := cliRunBudgets_placed)
    hDropNz hG hh hRead589 hreg

/-! ## Inner Encrypt (`w1_inner_placed_ok`) -/

/-- Discharges all 11 CLI hook contracts of `PublicApiEncHooksPlaced E2E.HooksE.A0` from
`CliGhostA0Hooks` and `hStrClone`. -/
theorem publicApiEncHooksPlaced_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hStrClone : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsStringCloneSym
      (stringCloneSpec E2E.HooksE.A0)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PublicApiEncHooksPlaced
      E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  shim := Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq
  alloc := Slots.cliExternsPlaced_alloc_sat mmpl gh W hG
  dealloc := Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG
  realloc := Slots.cliExternsPlaced_realloc_sat mmpl gh W hG
  memcpy := Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG
  stringClone := hStrClone
  timeAdd := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (Slots.cliExternsPlaced_timeAdd_sat mmpl W)
  durationSince := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
    (Slots.cliExternsPlaced_durationSinceBounded_sat mmpl W)
  handleError := Slots.cliGhostExterns_panic_handle_error mmpl gh W
  handleAllocError := Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W
  expectFailed := Slots.cliGhostExterns_panic_option_expect_failed mmpl gh W

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- `HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W))` from stock ghost hooks + `cliHookTablePlaced`. -/
theorem instHkdfPlacedHooks_cli
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook) :
    HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { memset := RunGlue.cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hMs
    memcpy := RunGlue.cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hMc
    compress256 := cliGhostExterns_row_eq mmpl gh W (Slots.compress256_row_placed mmpl W) }

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem new_from_slice_cro_ok_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 114)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (newFromSliceSpec W.C.F)) := by
  have hH : HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    instHkdfPlacedHooks_cli mmpl gh W hMs hMc
  have h114 := ConsumeMessageKeyTransfer.new_from_slice_placed_ok_withLsCodeLoaded_ro W.C.F
    hH.memcpy hH.compress256
  have hi_nf : subroutine_ok callerProg (lsmpl.base 114)
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec W.C.F with
          pre := fun x s0 =>
            (newFromSliceSpec W.C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
    ls_subroutine_ok_of_block h114 hi
  refine subroutine_ok_mono hi_nf ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  dsimp only [withLsCodeLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded] at hp ⊢
  have hcomm1 :
      ((newFromSliceSpec W.C.F).pre x s0 ∗
        ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        ((newFromSliceSpec W.C.F).pre x s0 ∗ R) := by ac_rfl
  have hcomm2 :
      (((newFromSliceSpec W.C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
        ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec W.C.F).pre x s0 ∗ R)) := by ac_rfl
  rw [hcomm1, satisfies_pure_sepConj] at hp
  rw [hcomm2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem new_from_slice_54_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook) :
    subroutine_ok
      ((blkPC_54).rebase (blkPl_54).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 114)
      { newFromSliceSpec W.C.F with
        pre := fun x s0 =>
          (newFromSliceSpec W.C.F).pre x s0 ∗
            ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ } :=
  new_from_slice_cro_ok_at_block mmpl gh W hMs hMc

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem hmac_cro_ok_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 73)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.LibsignalSession.hmacSpec W.C.F)) := by
  have hH : HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    instHkdfPlacedHooks_cli mmpl gh W hMs hMc
  have hi_hm := ConsumeMessageKeyTransfer.hmac_placed_ro_ok_at_block
    (callerProg := callerProg) (i := i) W.C.F hH.memcpy
    (hookMemset_eq_memsetHook.symm ▸ hH.memset) hH.compress256 hi
  refine subroutine_ok_mono hi_hm ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  dsimp only [withLsCodeLoaded, LibsignalTripleRatchet.withLsCodeRoLoaded] at hp ⊢
  have hcomm1 :
      ((CryptoVerification.LibsignalSession.hmacSpec W.C.F).pre x s0 ∗
        ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
        ((CryptoVerification.LibsignalSession.hmacSpec W.C.F).pre x s0 ∗ R) := by ac_rfl
  have hcomm2 :
      (((CryptoVerification.LibsignalSession.hmacSpec W.C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
        ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((CryptoVerification.LibsignalSession.hmacSpec W.C.F).pre x s0 ∗ R)) := by ac_rfl
  rw [hcomm1, satisfies_pure_sepConj] at hp
  rw [hcomm2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- Local callees of `OutgoingTripleRatchet::encrypt` (Block `428`) under `withLsCodeRoLoaded lsmpl`. -/
structure OtrRoCalleesPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  messageKeys :
    subroutine_ok ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 38) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (LibsignalTripleRatchet.Encrypt.messageKeysPlacedSpec W.C.F E2E.HooksE.A0))
  signalMessageNew :
    subroutine_ok ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 63) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (signalMessageNewSpec W.C.F E2E.HooksE.A0 uuidTryParse))
  nextChainKey :
    subroutine_ok ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 39) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (LibsignalTripleRatchet.Encrypt.nextChainKeyPlacedSpec W.C.F))

private theorem transfer_tr_cro_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono hcallee
      (fun x R s0 hp => by
        obtain ⟨hc, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
        dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
        have h1 : s0.mem ⊨ ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
          rw [satisfies_pure_sepConj]; exact ⟨⟨hc.1, hc.2⟩, hpre⟩
        exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1)
      (fun _ _ _ _ hq => hq)
  have htr := Initiate.transfer_withLsCodeRoLoaded (callerProg := callerProg) hcrl hi hj hj_unmut
  exact subroutine_ok_mono htr
    (fun x R s0 hp => by
      dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hp
      have hp' : s0.mem ⊨ ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) :=
        Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
      rw [satisfies_pure_sepConj] at hp'; obtain ⟨hc, hpre⟩ := hp'
      dsimp only [StoreKit.withLsCodeRoLoaded]
      have h1 : s0.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
        rw [satisfies_pure_sepConj]; exact ⟨⟨hc.1, hc.2⟩, hpre⟩
      exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1)
    (fun _ _ _ _ hq => hq)

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem generateKeys_428_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook) :
    subroutine_ok ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 69) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (generateKeysSpec W.C.F E2E.HooksE.A0)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have _ := instHkdfPlacedHooks_cli mmpl gh W hMs hMc
  have hext54 := LibsignalTripleRatchet.extract_placed_ok_of_inv W.C H
    (Inv := LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl)
    LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
    (new_from_slice_54_cro_ok mmpl gh W hMs hMc)
  have hext54' : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (extractSpec W.C.F)) := by
    refine subroutine_ok_mono hext54 (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hp ⊢
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) hp
  have hext69 := transfer_tr_cro_of_block (callerProg := (blkPC_69).rebase (blkPl_69).base H)
    (calleeProg := (blkPC_54).rebase (blkPl_54).base H) hext54'
  have hexp69 := LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := (blkPC_69).rebase (blkPl_69).base H)
      (LibsignalTripleRatchet.expand_multi_info_placed_ok W.C H))
  have hdealloc69 : subroutine_ok ((blkPC_69).rebase (blkPl_69).base H)
      (lsρ Keys.lsRustDeallocSym) (rustDeallocSpec E2E.HooksE.A0) :=
    E2E.Pqxdh.ResponderCore.pqxdh_placed_hook_ok_of_mem (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
  have hgk69 := Keys.generateKeys_placed_ok_of_contracts hext69 hexp69 hdealloc69
  have _ := CryptoVerification.instIsLsBlockProg_428 H
  exact transfer_tr_cro_of_block
    (callerProg := (CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
    (calleeProg := (blkPC_69).rebase (blkPl_69).base H) hgk69

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem signalMessageNew_428_placed_cro_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook) :
    subroutine_ok ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 63) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (signalMessageNewSpec W.C.F E2E.HooksE.A0 uuidTryParse)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hpks205 : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec E2E.HooksE.A0)) :=
    subroutine_ok_withLsCodeLoaded_of_plain (public_key_serialize_placed_ok
      (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
      (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W))
  have huuid252 : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
    refine subroutine_ok_mono (UuidFs.uuidTryParse_placed_okFs_F H)
      (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    dsimp only [withLsCodeLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2
  have hparse61 : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeSpec uuidTryParse)) :=
    parse_sid_placed_ok_at_of_code huuid252
  have hser61 : subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (blkPl_61).base
      (withLsCodeLoaded lsmpl (serializeAddressesSpec E2E.HooksE.A0 uuidTryParse)) :=
    serialize_addresses_placed_ok hparse61
      (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
      (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
      (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
  have hmac60 := computeMac_placed_cro_ok W.C E2E.HooksE.A0 H
    (new_from_slice_cro_ok_at_block mmpl gh W hMs hMc
      (callerProg := (blkPC_60).rebase (blkPl_60).base H))
    (LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (callerProg := (blkPC_60).rebase (blkPl_60).base H) hpks205))
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_compress256Multi_sat mmpl W))
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG)
  have hnew63 := signalMessageNew_placed_cro_ok
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W)
    (ls_subroutine_ok_of_block (callerProg := (blkPC_63).rebase (blkPl_63).base H) hpks205)
    (ls_subroutine_ok_of_block (callerProg := (blkPC_63).rebase (blkPl_63).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain (Prost.encoded_len_placed_ok E2E.HooksE.A0 H)))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_63).rebase (blkPl_63).base H)
      (Prost.encode_varint_placed_ok
        (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
        (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
        (Slots.cliExternsPlaced_realloc_sat mmpl gh W hG)
        (Slots.cliGhostExterns_panic_handle_error mmpl gh W)))
    (ls_subroutine_ok_of_block (callerProg := (blkPC_63).rebase (blkPl_63).base H) hser61)
    (transfer_tr_cro_of_block (callerProg := (blkPC_63).rebase (blkPl_63).base H)
      (calleeProg := (blkPC_60).rebase (blkPl_60).base H) hmac60)
  have _ := CryptoVerification.instIsLsBlockProg_428 H
  exact transfer_tr_cro_of_block
    (callerProg := (CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
    (calleeProg := (blkPC_63).rebase (blkPl_63).base H) hnew63

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem otrRoCalleesPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook) :
    OtrRoCalleesPlacedOk mmpl gh W := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have _ := CryptoVerification.instIsLsBlockProg_428 H
  refine
    { messageKeys := transfer_tr_cro_of_block
        (callerProg := (CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
        (calleeProg := (blkPC_38).rebase (blkPl_38).base H)
        (message_keys_placed_cro_ok
          (hmac_cro_ok_at_block mmpl gh W hMs hMc (callerProg := (blkPC_38).rebase (blkPl_38).base H))
          (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
          (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
          (Slots.cliGhostExterns_panic_handle_error mmpl gh W))
      signalMessageNew := signalMessageNew_428_placed_cro_ok mmpl gh W hG hMs hMc
      nextChainKey := transfer_tr_cro_of_block
        (callerProg := (CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
        (calleeProg := (blkPC_39).rebase (blkPl_39).base H)
        (next_chain_key_placed_cro_ok
          (hmac_cro_ok_at_block mmpl gh W hMs hMc (callerProg := (blkPC_39).rebase (blkPl_39).base H))
          (Slots.cliGhostExterns_panic_all mmpl gh W lsPanicConstAddOverflowSym (by decide))) }

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
private theorem otrEncryptV1_464_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    subroutine_ok (CryptoVerification.CliRatchet.EncPlaced.lsProg_464
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQT
          SpqrV1.GF.Mul2U16.tokenInitPlacedAt W.C E2E.HooksE.A0 0#64 uuidTryParse (pqxdhSpqrModel ⟨W.C, W.Q⟩))) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl gh W hG hMs hMc
  have _ := CryptoVerification.CliRatchet.SendPlaced.instIsLsBlockProg_427 H
  have _ := CryptoVerification.CliRatchet.EncPlaced.instIsLsBlockProg_464 H
  have hSend428 : subroutine_ok
      ((CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
      (lsmpl.base 427) (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT E2E.HooksE.A0 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩))) :=
    StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl (StoreKit.ls_subroutine_ok_rocl_of_block
      (callerProg := (CryptoVerification.blkPC_428).rebase (CryptoVerification.blkPl_428).base H)
      hSpqr.spqrSendCoins (by decide) (by decide) (by decide))
  have h428 := CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.otrEncryptV1_coins_placed_ok
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt W.C E2E.HooksE.A0 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) H
    hAesEnc
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_formatInner_sat mmpl W))
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    hSend428
    hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl gh W hG hMs hMc)
    hOtrRo.signalMessageNew hOtrRo.nextChainKey
  change subroutine_ok _ (lsmpl.base 428 + 0#64) _; rw [BitVec.add_zero]
  exact StoreKit.ls_subroutine_ok_rocl_of_block
    (callerProg := CryptoVerification.CliRatchet.EncPlaced.lsProg_464 H)
    (j := 428) h428 (by decide) (by decide) (by decide)

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Transfers the empty-SPQR `OutgoingTripleRatchet::encrypt` contract from Block `428` to Block `464`. -/
theorem otrEncryptEmpty_464_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (S : SpqrModel) (hEmpty : S.SendEmptyOk)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0)) :
    subroutine_ok (CryptoVerification.CliRatchet.EncPlaced.lsProg_464
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ
          (· = []) W.C E2E.HooksE.A0 0#64 uuidTryParse S)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hOtrRo := otrRoCalleesPlacedOk_cli mmpl gh W hG hMs hMc
  have _ := CryptoVerification.CliRatchet.EncPlaced.instIsLsBlockProg_464 H
  have h428 := CryptoVerification.Cli.LibsignalTripleRatchet.Encrypt.otrEncryptEmpty_coins_placed_ok
    W.C E2E.HooksE.A0 0#64 S H hEmpty
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    hAesEnc
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_formatInner_sat mmpl W))
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    hOtrRo.messageKeys (generateKeys_428_placed_ok mmpl gh W hG hMs hMc)
    hOtrRo.signalMessageNew hOtrRo.nextChainKey
  change subroutine_ok _ (lsmpl.base 428 + 0#64) _; rw [BitVec.add_zero]
  exact StoreKit.ls_subroutine_ok_rocl_of_block
    (callerProg := CryptoVerification.CliRatchet.EncPlaced.lsProg_464 H)
    (j := 428) h428 (by decide) (by decide) (by decide)

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Proves `W1InnerPlacedOk` on Block `464` from `SpqrV1PlacedSeams`, `hDropNz`, and `A0` ghost/AES hooks. -/
theorem w1_inner_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    EncryptLemmas.W1InnerPlacedOk mmpl gh W cliRunBudgets_placed Slots.scopeIn := by
  intro F peer hok
  have hq : (EncryptLemmas.w1SessKitPlaced cliRunBudgets_placed F peer).Quiet ∧
      (EncryptLemmas.w1IdKitPlaced cliRunBudgets_placed F peer).Quiet :=
    ⟨⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩,
     ⟨fun _ _ _ _ => NoFsEv.nil, fun _ _ _ => NoFsEv.nil⟩⟩
  have hempty : (pqxdhSpqrModel ⟨W.C, W.Q⟩).SendEmptyOk := LibsignalSpqrV1.spqrV1_emptyOk W.C.F W.Q.K
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_placed_okVT_fs_cli
    (F0 := SpqrV1.GF.Mul2U16.tokenInitPlacedAt)
    (publicApiEncHooksPlaced_cli mmpl gh W hG hh.stringClone)
    (w1SessKitPlaced_okSE mmpl gh W cliRunBudgets_placed hDropNz hh hRead589 F peer)
    (KitInst.cliIdKitOkIE_cli_placed mmpl gh W (F0 := F) (peer := peer)
      (readStk := cliRunBudgets_placed.readFile)
      (readProg := Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jRead := 589)
      hDropNz hh hRead589 (by decide) (Nat.le_refl _) (by decide) (Nat.le_refl _))
    (otrEncryptV1_464_placed_ok mmpl gh W hG hMs hMc hAesEnc hSpqr)
    (otrEncryptEmpty_464_placed_ok mmpl gh W (pqxdhSpqrModel ⟨W.C, W.Q⟩) hempty hG hMs hMc hAesEnc)
    (w2SessVt_placed_ok cliRunBudgets_placed hDropNz F peer)
    (w2IdVt_placed_ok cliRunBudgets_placed hDropNz F peer)
    (Or.inr ⟨hq, hh.fs
      (CryptoVerification.CliRatchet.EncPlaced.lsProg_464
        (cliGhostExterns gh (cliExternsPlaced mmpl W))) 464⟩)
    (fun r ⟨hsc, _⟩ => Slots.scopeKit_recordInScopeEnc hsc)
    (fun r s ⟨hsc, _⟩ hsess => Slots.scopeKit_pqrState_lt hsc s hsess)
    (fun {x r sess otr taken k m otr'} haddr h15 =>
      Slots.cliEncRecOk_opened (A := E2E.HooksE.A0) (b := 0#64) (pathOk := cliWrOk)
        (Scope₀ := Slots.scopeIn) (F0 := F) (peer := peer) (s1 := 0) (s2 := 0) (s3 := 0) (s4 := 0)
        (C := W.C) (K := W.Q.K) (parse := uuidTryParse) (fun _ h => h) hok haddr h15)

/-! ## Initiation Callees and `CliSlotCalleesPlaced` Assembly -/

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem w3Hooks_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    Initiate.RunHooksPlaced W E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { alloc := hh.alloc
    allocFs := hh.allocFs
    codec := Slots.codecHooksPlaced_cli mmpl gh W hG
    ser := Proofs.libsignal.Hooks2.serContractsXPlaced_of_stage2ContractsMinPlaced
      (Slots.stage2ContractsMinPlaced_cli mmpl gh W hG)
    shim := Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq
    rawAlloc := Slots.cliExternsPlaced_alloc_sat mmpl gh W hG
    rawDealloc := Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG
    framelessMemcpy := Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG
    sessionMemcpyRegion := Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG
    memcpyRO := hh.memcpyRO
    bcmp := hh.bcmp
    e2eBcmp := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_e2eBcmp_sat mmpl W)
    allocZeroed := hh.allocZeroed
    stringClone := hh.stringClone
    formatInner := hh.formatInner
    pubFromSecret := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_derivePublicKeyBytes_sat mmpl W)
    dh := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_diffieHellman_sat mmpl W)
    sharedDrop := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_sharedSecretDrop_sat mmpl W)
    staticDrop := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W)
    blackBox := cliExternsPlaced_blackBox_eq mmpl gh W
    hkdf := instHkdfPlacedHooks_cli mmpl gh W hMs hMc
    kemEncaps := cliGhostExterns_row_eq mmpl gh W (Slots.kemEncaps_row_placed mmpl W)
    durationSince := cliGhostExterns_row_eq mmpl gh W (Slots.durationSince_row_placed mmpl W)
    panic_alloc := hh.panics "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" (by decide)
    panic_raw := hh.panics "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" (by decide)
    panic_sym := hh.panics
    fs := fun {prog} {i} (_ : IsLsBlockProg prog i _) => hh.fs prog i }

private theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} :
    subroutine_ok prog (lsmpl.base 46) (sessDeserializeSpecPlaced (fun _ => False) A) :=
  subroutine_ok.of_codeLoaded fun _ _ _ _ _ hpre _ _ => by
    obtain ⟨_, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact False.elim hpre.1.2.2.2

private theorem w3DirPut_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (Placed.lsProg_542 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 542)
      (dirPutSpecPlaced E2E.HooksE.A0 Initiate.cliDirPutStk) :=
  Put.dirPut_placed_caller_ok_of_deps
    (callerProg := Placed.lsProg_542 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 542) hh.alloc hh.bcmp
    (growProg := Placed.lsProg_586 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (jGrow := 586)
    (by decide) (by decide) (SessKit.cliGrowOneDir_placed_ok hh.alloc hh.panics)
    (Nat.le_refl SessKit.dirPutNeedPlaced) (by decide)

theorem w3Exist_placed_ok_of_putStr [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile)) :
    Initiate.ExistingStoreCalleesPlaced E2E.HooksE.A0
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) cliRunBudgets_placed := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have hAddr := SessKit.cliAddrText_placed_ok hh
  have hGet : subroutine_ok (Placed.lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.dirGetNeed) :=
    SessKit.cliDirGet_placed_ok
      (readProg := Placed.lsProg_589 H) (jRead := 589)
      (fun _ hp => hp.2) hh
      (RunSkeleton.cliReadFilePlaced_rocl_ok mmpl gh W cliRunBudgets_placed.readFile hRead589)
      (by decide) (by decide)
  have hPutStr' : subroutine_ok (Placed.lsProg_543 H) (lsmpl.base 543)
      (dirPutStrSpecPlaced E2E.HooksE.A0 Initiate.cliDirPutStrStk) :=
    dirPutStrPlacedOk_cli mmpl gh W hh
  have hEq := Store.IdTrustPoll.publicKeyEq_placed_ok_of_bb (cliExternsPlaced_blackBox_eq mmpl gh W)
  have hDec := RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok
    (A := E2E.HooksE.A0) H
  exact
    { dirGet := hGet
      addressText := hAddr
      dirPut := w3DirPut_placed_ok mmpl gh W hh
      idTrustShim := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact Store.IdTrustShim.idTrustShim_placed_ok_of_deps hh.alloc hh.panics (by omega)
      idTrustPoll := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have := Initiate.stk_sub_ge_dirGet hstk
        have : extHookStack ≤ 65536 := by decide
        exact Store.IdTrustPoll.idTrustPoll_placed_ok_of_deps hh.alloc hGet hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      sessLoadShim := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have : 0x20 + extHookStack ≤ 516880 := by decide
        exact Store.LoadShim.sessLoadShim_placed_ok_of_deps hh.alloc hh.panics (by omega)
      sessLoadPoll := fun {stk} hstk =>
        Store.LoadPoll.sessLoadPoll_placed_ok_of_deps hh.alloc hAddr hGet
          (sessDeserialize_false_placed_ok (prog := Placed.lsProg_569 H))
          (hh.fs (Placed.lsProg_569 H) 569)
          (Initiate.sessLoadPoll_stk_le (by decide) hstk)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      idSaveShim := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact Store.IdSaveShim.idSaveShim_placed_ok_of_deps hh.alloc hh.panics (by omega)
      idSavePoll := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have := Initiate.stk_sub_ge_dirGet hstk
        have : Initiate.cliDirPutStrStk ≤ 65536 := by decide
        have : publicKeySerializeStackX ≤ 65536 := by decide
        have : extHookStack ≤ 65536 := by decide
        exact Store.IdSavePoll.idSavePoll_placed_ok_of_deps hh.alloc hh.panics hGet hPutStr'
          hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      sessStoreShim := fun {stk} hstk => by
        have := Initiate.stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact Store.StoreShim.sessStoreShim_placed_ok_of_deps hh.alloc hh.panics (by omega)
      rodata_idVt_keyPairSlot := KitInst.rodata_cliIdentity_kpSlot_placed
      rodata_idVt_regIdSlot := KitInst.rodata_cliIdentity_regIdSlot_placed
      rodata_idVt_saveSlot := KitInst.rodata_cliIdentity_saveSlot_placed
      rodata_idVt_trustSlot := KitInst.rodata_cliIdentity_trustSlot_placed
      rodata_sessVt_loadSlot := KitInst.rodata_cliSession_loadSlot_placed
      rodata_sessVt_storeSlot := KitInst.rodata_cliSession_storeSlot_placed }

/-- Block-`33` `set_unacknowledged_pre_key_message` contract obligation. -/
def SetUnackEpochPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 33)
    (StoreKit.withLsCodeRoLoaded lsmpl (Initiate.setUnackPreKeyMsgEpochInnerSpec E2E.HooksE.A0))

theorem setUnackEpochPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    SetUnackEpochPlacedOk mmpl gh W :=
  Slots.setUnackPreKeyMsg_exact_stack_epoch_placed_ok_cli mmpl gh W
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliGhostExterns_panic_handle_error mmpl gh W)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_durationSinceEpochAlloc_sat mmpl W))

private theorem w3VerifySigHooks_cli
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    E2E.Pqxdh.Shared.VerifySignaturePlacedHooks
      (E2E.modelPrims X ⟨W.C, W.Q⟩) (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { memcpy := Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG
    memset := Slots.cliExternsPlaced_sessionMemset_sat mmpl gh W hG E2E.Pqxdh.Shared.pqxdhHookStack (by decide)
    blackBox := cliExternsPlaced_blackBox_eq mmpl gh W
    montToEd := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_toEdwards_sat mmpl W X (img := default))
    compress := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_compress_sat mmpl W)
    edNeg := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_edNeg_sat mmpl W)
    sha512Compress := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_compress512_sat mmpl W X (img := default))
    scalarWide := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_scalarWide_sat mmpl W)
    scalarMod := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_scalarMod_sat mmpl W)
    doubleMul := Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_dsmb_sat mmpl W X (img := default)) }

private theorem w3VerifySignature_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 203)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (Initiate.verifySignatureInnerSpec (E2E.modelPrims X ⟨W.C, W.Q⟩))) := by
  have hv := E2E.Pqxdh.Shared.verifySignature_placed_ok_of_block
    (callerProg := Initiate.initProgPlaced mmpl gh W)
    (E2E.Pqxdh.Shared.VerifySignaturePrims.of_structuralPrims
      (E2E.Pqxdh.Initiator.structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩))
    (w3VerifySigHooks_cli mmpl gh W X hG) (by decide)
  refine subroutine_ok_map hv (fun g R s0 hp =>
    ⟨{ pkPtr := g.pkPtr, msgPtr := g.msgPtr, sigPtr := g.sigPtr,
       pk := g.pk, m := g.m, sig := g.sig }, R, ?_, fun _ hq => hq⟩)
  obtain ⟨hc, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
  dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
  have h1 : s0.mem ⊨ ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      ((E2E.Pqxdh.Shared.verifySignatureCallSpec (E2E.modelPrims X ⟨W.C, W.Q⟩)).pre
        { pkPtr := g.pkPtr, msgPtr := g.msgPtr, sigPtr := g.sigPtr,
          pk := g.pk, m := g.m, sig := g.sig } s0 ∗ R) := by
    rw [satisfies_pure_sepConj]; exact ⟨⟨hc.1, hc.2⟩, hpre⟩
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1

private theorem w3IsSameAccount_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 17)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec E2E.HooksE.A0 uuidTryParse)) := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (uuidTryParseCodeSpec uuidTryParse)) := by
    refine subroutine_ok_mono (UuidFs.uuidTryParse_placed_okFs_F H)
      (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    dsimp only [withLsCodeLoaded, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2
  have hisa := E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_placed_ok_at E2E.HooksE.A0
    (callerProg := Initiate.initProgPlaced mmpl gh W)
    (cliExternsPlaced_blackBox_eq mmpl gh W) huuid (by decide)
  refine subroutine_ok_mono hisa (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hc, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
  dsimp only [withLsCodeLoaded]
  have h1 : s0.mem ⊨ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
      ((E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec E2E.HooksE.A0 uuidTryParse).pre x s0 ∗ R) := by
    rw [satisfies_pure_sepConj]; exact ⟨hc.1, hpre⟩
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1

private theorem w3CalculateAgreement_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 207)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (Initiate.pqxdhCalculateAgreementPlacedInnerSpec (E2E.modelPrims X ⟨W.C, W.Q⟩) E2E.HooksE.A0)) := by
  have hca := E2E.Pqxdh.ResponderCore.pqxdhCalculateAgreement_placed_ok_of_block
    (callerProg := Initiate.initProgPlaced mmpl gh W)
    (E2E.Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_diffieHellman_sat mmpl W))
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_sharedSecretDrop_sat mmpl W))
    (cliExternsPlaced_blackBox_eq mmpl gh W)
    (Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq)
    (Slots.cliExternsPlaced_alloc_sat mmpl gh W hG)
    (Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_staticSecretDrop_sat mmpl W))
    (Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W) (by decide)
  refine subroutine_ok_mono hca (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  obtain ⟨hc, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
  dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
  have h1 : s0.mem ⊨ ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
      ((E2E.Pqxdh.ResponderCore.pqxdhCalculateAgreementPlacedBaseSpec
        (E2E.Pqxdh.ResponderCore.ofSignalPqxdhPrimitives (E2E.modelPrims X ⟨W.C, W.Q⟩))
        E2E.HooksE.A0).pre x s0 ∗ R) := by
    rw [satisfies_pure_sepConj]; exact ⟨⟨hc.1, hc.2⟩, hpre⟩
  exact Eq.mp (congrArg (s0.mem ⊨ ·) (by ac_rfl)) h1

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
theorem w3A4_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    Initiate.SubsetA4InitCalleesPlaced E2E.HooksE.A0 mmpl gh W := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  have _ := instHkdfPlacedHooks_cli mmpl gh W hMs hMc
  have _ := CryptoVerification.instIsLsBlockProg_59 H
  have _ := CryptoVerification.instIsLsBlockProg_207 H
  exact
    { verifySignature := fun X => w3VerifySignature_placed_ok mmpl gh W X hG
      isSameAccount := w3IsSameAccount_placed_ok mmpl gh W
      calculateAgreement := fun X => w3CalculateAgreement_placed_ok mmpl gh W X hG
      spqrInitialState := hSpqr.spqrInitialState_initProg
      setUnackPreKeyMsg := setUnackEpochPlacedOk_cli mmpl gh W hG
      pqxdhHkdfExtract := fun X => E2E.Pqxdh.ResponderCore.pqxdhHkdfExtract_placed_ok
        (E2E.Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      pqxdhHkdfExpand := fun X => E2E.Pqxdh.ResponderCore.pqxdhHkdfExpandMultiInfo_placed_ok
        (E2E.Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
      ctEqSliceRO := ls_subroutine_ok_of_block
        (callerProg := (CryptoVerification.blkPC_207).rebase (CryptoVerification.blkPl_207).base H)
        (ConsumeMessageKeyTransfer.ct_eq_ro_placed_ok_withLsCodeLoaded
          (cliExternsPlaced_blackBox_eq mmpl gh W))
      newFromSlice := new_from_slice_54_cro_ok mmpl gh W hMs hMc }

/-- Block-`618` `coinsFillSpecPlacedW3` contract obligation for `cliCoinsFillStack ≤ cStk`. -/
def CoinsFillCliPlacedOk [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop :=
  ∀ {cStk : Nat}, Initiate.cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
    subroutine_ok (Initiate.initProgPlaced mmpl gh W) (lsmpl.base 618)
      (StoreKit.withLsCodeRoLoaded lsmpl (Initiate.coinsFillSpecPlacedW3 cStk))

theorem coinsFillCliPlacedOk_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    CoinsFillCliPlacedOk mmpl gh W := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  intro cStk hstk hstk64
  have hge : 80 ≤ cStk := by unfold Initiate.cliCoinsFillStack extHookStack at hstk; omega
  obtain ⟨fMc, hfMc, _, _, _, hMcSessReg, _, _, hMcFs, _⟩ := hG.memcpy
  obtain ⟨fMs, hfMs, _, _, _, hMsSessReg, hMsFs, _⟩ := hG.memset
  have hmc618 : subroutine_ok
      ((CryptoVerification.SignalSession.Coins.Placed.blkPC_618).rebase
        (CryptoVerification.SignalSession.Coins.Placed.blkPl_618).base H)
      (lsρ memcpyName) (StoreKit.withLsRoCl lsmpl (withStack sessionMemcpyRegionSpec (cStk - 80)).keepsFs) :=
    StoreKit.subroutine_ok_rocl_of_plain (E2E.Pqxdh.ResponderCore.pqxdh_placed_hook_ok_of_mem
      ⟨fMc, RunGlue.cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hfMc,
        (hookOk_withStack hMcSessReg (cStk - 80)).keepsFs hMcFs⟩)
  have hms618 : subroutine_ok
      ((CryptoVerification.SignalSession.Coins.Placed.blkPC_618).rebase
        (CryptoVerification.SignalSession.Coins.Placed.blkPl_618).base H)
      (lsρ memsetName) (StoreKit.withLsRoCl lsmpl (withStack sessionMemsetRegionSpec (cStk - 80)).keepsFs) :=
    StoreKit.subroutine_ok_rocl_of_plain (E2E.Pqxdh.ResponderCore.pqxdh_placed_hook_ok_of_mem
      ⟨fMs, RunGlue.cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hfMs,
        (hookOk_withStack hMsSessReg (cStk - 80)).keepsFs hMsFs⟩)
  have h618 := Initiate.signal_session_coins_fill_placed_ok_of_mc_ms hge hstk64 hmc618 hms618
  have hmono : subroutine_ok
      ((CryptoVerification.SignalSession.Coins.Placed.blkPC_618).rebase
        (CryptoVerification.SignalSession.Coins.Placed.blkPl_618).base H)
      (lsmpl.base 618) (StoreKit.withLsCodeRoLoaded lsmpl (Initiate.coinsFillSpecPlacedW3 cStk)) :=
    subroutine_ok_mono h618 (fun _ _ _ hp => (StoreKit.extract_withLsCodeRoLoaded hp).2) (fun _ _ _ _ hq => hq)
  have _ := CryptoVerification.SignalSession.Coins.Placed.instIsLsBlockProg_618 H
  exact Initiate.transfer_withLsCodeRoLoaded (callerProg := Initiate.initProgPlaced mmpl gh W) hmono

theorem w3Stage2_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (S : RunSem) (_hS : S.initiate = initDef X ⟨W.C, W.Q⟩) :
    Initiate.Stage2PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S :=
  fun hh _hCoins hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs2 hpost hpanic hnext =>
    Initiate.initiate_stage2_placed_ok hh
      (fun {cStk} => coinsFillCliPlacedOk_cli mmpl gh W hG (cStk := cStk))
      hStore hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs2 hpost hpanic hnext

theorem w3Stage3_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (S : RunSem) (_hS : S.initiate = initDef X ⟨W.C, W.Q⟩) :
    Initiate.Stage3PlacedOk E2E.HooksE.A0 mmpl gh W X cliRunBudgets_placed S :=
  fun hh _hCoins hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpost hpanic hnext =>
    Initiate.initiate_stage3_placed_ok hh
      (fun {cStk} => coinsFillCliPlacedOk_cli mmpl gh W hG (cStk := cStk))
      hLocal hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpost hpanic hnext

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `CliSlotCalleesPlaced mmpl gh X W` from the Block-`463` `region_ok` hypothesis `hreg`. -/
theorem cliSlotCallees_placed_of_region [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hreg : region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTight
        W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩)).withVRegs.restrictPre
        ((fun _ => True) ·.st.pqRatchetState))) :
    CliSlotCalleesPlaced mmpl gh X W :=
  { w1Inner := w1_inner_placed_ok mmpl gh W hDropNz hG hMs hMc hh hRead589 hAesEnc hSpqr
    w2SessVt := w2SessVt_placed_ok cliRunBudgets_placed hDropNz
    w2IdVt := w2IdVt_placed_ok cliRunBudgets_placed hDropNz
    w2Inner := w2_inner_placed_ok_of_region mmpl gh W hDropNz hG hh hRead589 hreg
    w3Hooks := w3Hooks_placed_ok mmpl gh W hG hMs hMc hh
    w3Exist := w3Exist_placed_ok_of_putStr mmpl gh W hh hRead589
    w3A4 := w3A4_placed_ok mmpl gh W hG hMs hMc hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl gh X W hG
    w3Stage3 := w3Stage3_placed_ok mmpl gh X W hG }

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `CliSlotCalleesPlaced mmpl gh X W` from `SpqrV1PlacedSeams` and the Block-`462`
`logClosurePlacedSpec` seam `hLog462`. -/
theorem cliSlotCallees_placed_of_seams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hLog462 : subroutine_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 462)
      (withLsCodeLoaded lsmpl
        CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) :
    CliSlotCalleesPlaced mmpl gh X W :=
  { w1Inner := w1_inner_placed_ok mmpl gh W hDropNz hG hMs hMc hh hRead589 hAesEnc hSpqr
    w2SessVt := w2SessVt_placed_ok cliRunBudgets_placed hDropNz
    w2IdVt := w2IdVt_placed_ok cliRunBudgets_placed hDropNz
    w2Inner := DecryptLemmas.w2_inner_placed_ok mmpl gh W hDropNz hG hh hRead589 hAesDec hSpqr hLog462
    w3Hooks := w3Hooks_placed_ok mmpl gh W hG hMs hMc hh
    w3Exist := w3Exist_placed_ok_of_putStr mmpl gh W hh hRead589
    w3A4 := w3A4_placed_ok mmpl gh W hG hMs hMc hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl gh X W hG
    w3Stage3 := w3Stage3_placed_ok mmpl gh X W hG }

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Assembles `CliSlotCalleesFullPlaced mmpl gh X W` under `[LibsignalFullPlacement]` from the
`withLsFrozen` Block-`463` `region_ok` hypothesis `hreg`. -/
theorem cliSlotCallees_full_placed_of_region [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W)
    (hreg : region_ok
      (CryptoVerification.CliRatchet.DecPlaced.lsProg_463
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
      ((withLsFrozen lsmpl
        (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.recordDecryptPlacedSpecTPTight
          W.C E2E.HooksE.A0 0#64 uuidTryParse (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))).withVRegs.restrictPre
        (fun _ => True))) :
    CliSlotCalleesFullPlaced mmpl gh X W :=
  { w1Inner := w1_inner_placed_ok mmpl gh W hDropNz hG hMs hMc hh hRead589 hAesEnc hSpqr
    w2SessVt := w2SessVt_placed_ok cliRunBudgets_placed hDropNz
    w2IdVt := w2IdVt_placed_ok cliRunBudgets_placed hDropNz
    w2Inner := w2_inner_frozen_placed_ok_of_region mmpl gh W hDropNz hG hh hRead589 hreg
    w3Hooks := w3Hooks_placed_ok mmpl gh W hG hMs hMc hh
    w3Exist := w3Exist_placed_ok_of_putStr mmpl gh W hh hRead589
    w3A4 := w3A4_placed_ok mmpl gh W hG hMs hMc hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl gh X W hG
    w3Stage3 := w3Stage3_placed_ok mmpl gh X W hG }

-- A2'' D1: A0 island, hMs/hMc discharged at a0Ghost
/-- Closed `[LibsignalFullPlacement]` assembly of `CliSlotCalleesFullPlaced mmpl gh X W` from
`SpqrV1PlacedSeams` and `A0` hooks (`w2Inner` discharged via `w2_inner_full_placed_ok`). -/
theorem cliSlotCallees_full_placed_of_seams [LibsignalFullPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (X : UnreachedPqxdhPrimitives)
    (W : CliHooks)
    (hDropNz : lsmpl.base 547 ≠ 0#64)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some CryptoVerification.LibsignalAesCbc.memsetHook)
    (hMc : gh.memcpy = some CryptoVerification.LibsignalAesCbc.memcpyHook)
    (hh : RunSkeleton.RunHooksPlaced E2E.HooksE.A0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hRead589 : subroutine_ok (Placed.lsProg_589 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (readFileSpecPlaced cliIo.rd cliWrOk E2E.HooksE.A0 cliRunBudgets_placed.readFile))
    (hAesEnc : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesEncSym
      (aesEncSpec W.C.E E2E.HooksE.A0))
    (hAesDec : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsAesDecSym
      (aesDecSpec W.C.D E2E.HooksE.A0))
    (hSpqr : SpqrV1PlacedSeams mmpl gh W) :
    CliSlotCalleesFullPlaced mmpl gh X W :=
  { w1Inner := w1_inner_placed_ok mmpl gh W hDropNz hG hMs hMc hh hRead589 hAesEnc hSpqr
    w2SessVt := w2SessVt_placed_ok cliRunBudgets_placed hDropNz
    w2IdVt := w2IdVt_placed_ok cliRunBudgets_placed hDropNz
    w2Inner := DecryptLemmas.w2_inner_full_placed_ok mmpl gh W hDropNz hG hh hRead589 hAesDec hSpqr
    w3Hooks := w3Hooks_placed_ok mmpl gh W hG hMs hMc hh
    w3Exist := w3Exist_placed_ok_of_putStr mmpl gh W hh hRead589
    w3A4 := w3A4_placed_ok mmpl gh W hG hMs hMc hSpqr
    w3Stage2 := w3Stage2_placed_ok mmpl gh X W hG
    w3Stage3 := w3Stage3_placed_ok mmpl gh X W hG }

end CryptoVerification.SignalSession.Cli.MainHops
