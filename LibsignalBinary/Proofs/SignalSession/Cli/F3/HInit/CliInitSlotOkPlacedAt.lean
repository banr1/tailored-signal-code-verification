/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
public import LibsignalBinary.Specifications.LibsignalE2E.HooksMallocng
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.FsTrace
import ProofLib.Hoare.MultiCodeROHook
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `initiate` Slot Producer (`CliInitSlotOkPlacedAt`)

Establishes the Block-579 / Block-521 `initiate` slot contract `CliInitSlotOkPlacedAt` over
`cliGhostExterns gh' (cliExternsPlaced mmpl W)`:
- `TraceDeltaNoAllocFailed` / `ExternNoAllocFailed`: append-delta trace invariant refuting
  `allocFailedIn` across `Syscall.standard`, `codeROSubroutineHook`, and `cliHookTablePlaced`;
- `W3GhostHooks`: minimal `initiate` ghost-hook bundle parametric in `gh'` and `lsReadFileSym`;
- `cliInitSlotOkPlacedAt_of_ghost` and `stage3OkEvents` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open CryptoGames.CBC (AesKey Block)
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_40 blkPC_59 blkPC_207
   blkPl_40 blkPl_59 blkPl_207 libsignalMutatedBlocks lsProg_40 lsProg_59 lsRustNoAllocShimSym
   ls_hook_ok_ultra_of_mem lsmpl lsρ)
open CryptoVerification.E2E
  (PqxdhPrims PreKeyBundleFields UnreachedPqxdhPrimitives aesDecHookMallocng aesEncHookMallocng
   compress512Hook compressHook dsmbHook edNegHook fmtWriteHook0 formatInnerHook0 initiateInput
   kemDecapsHook kemEncapsHook libcruxHmacHookMallocng mlkemDecapsHook mlkemEncaps1Hook
   mlkemEncaps2Hook mlkemFromSeedHook mlkemPk1Hook mlkemPk2Hook mlkemValidatePkHook modelPrims
   restoreCallerRegs scalarModHook scalarWideHook stepRustAlloc1 stepRustDealloc1 timeAddHook
   toEdwardsHook torsionFreeHook)
open CryptoVerification.E2E.Pqxdh.Initiator (structuralPrims_initiatorModelPrims)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (ofSignalPqxdhPrimitives primitivesMatchCrypto_modelPrims)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded subroutine_ok_rocl_of_plain withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet
  (HkdfPlacedHooks diffieHellmanHook extHookStack keys_ls_hook_ok_of_mem
   keys_ls_subroutine_ok_of_block_cro noAllocShimSpec pubFromSecretHook publicKeySerializeStackX
   withStack zeroizeSecretHook)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (CliHooks cliBcmpHook cliExternsPlaced cliHookTablePlaced cliPqxdhHookTablePlaced
   durationSinceExactHook fromUtf8Hook lsFormatInnerSym lsReadFileSym lsStringCloneSym memrchrHook
   strlenHook unitResult writeFileHook writeStdoutHook)
open CryptoVerification.SignalSession.Cli.KitInst
  (rodata_cliIdentity_kpSlot_placed rodata_cliIdentity_regIdSlot_placed
   rodata_cliIdentity_saveSlot_placed rodata_cliIdentity_trustSlot_placed
   rodata_cliSession_loadSlot_placed rodata_cliSession_storeSlot_placed)
open CryptoVerification.SignalSession.Cli.KitInst.SessKit (dirPutNeedPlaced)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo cliRunBudgets cliWrOk)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_542 lsProg_543 lsProg_569 lsProg_586 lsProg_589)
open CryptoVerification.SignalSession.Cli.Run.Placed (instIsLsBlockProg_579 lsProg_579)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunNeeds RunSem mkSlot)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks IsFsC cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs
  (InitOk₀ cliInitiateFrame cliInitiateNeed initDef padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced AtStage3Placed AtStage4Placed cliCoinsFillStack cliCoinsFillStackPlaced
   cliDirPutStk initEntryPlaced initProgPlaced sessLoadPoll_stk_le stk_sub_ge_base
   stk_sub_ge_dirGet transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunSkeleton (CalleeSlot.OkPlaced RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (filesOk₀ scopeIn)
open CryptoVerification.SignalSession.Coins.Placed (blkPC_618 blkPl_618)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (formatInnerBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (handshakeKeysDerive_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (ct_eq_ro_placed_vm_ok_of_block expand_multi_info_placed_vm_ok_of_other_block)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
  (pqxdhHkdfExpandMultiInfo_placed_ok pqxdhHkdfExtract_placed_ok)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat pqxdhHkdfExpandMultiInfo_placed_ok_sat
   pqxdhHkdfExtract_placed_ok_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudget (dirPut_placed_caller_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudget (dirPutStr_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (hRead_withLsCodeRoLoaded_of_hookSat)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliAddrText_placed_ok cliDirGet_placed_ok cliGrowOneDir_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetAux
  (cliExistingStoreCalleesEnvs w3HkdfExtract40_cro_placed_ok w3IsSameAccount_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams
  (CliSlotEnvs SpqrV1PlacedSeamsBudget cliDirPutStrNeedPlaced cliGhostExterns_blackBox_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
  (CliInitiateBudgetFits Stage1StepWitness Stage2StepWitness Stage3PlacedOk
   subroutine_ok_of_sepWPp_init_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (signal_session_coins_fill_placed_ok_at_init)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
  (signal_session_coins_fill_vm_placed_ok_at_init signal_session_coins_fill_vm_placed_ok_of_mc_ms)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (instHkdfPlacedHooks_cliGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced SubsetA4InitCalleesPlaced calculateAgreement_cli_placed_ok
   derivePubKeyBytes_cli_placed_ok dropSessionStructure_cli_placed_ok kemCtSerialize_cli_placed_ok
   kemPublicKeySerialize_local2_placed_ok promoteState_cli_placed_ok sessionStateNew_cli_placed_ok
   setKyberCiphertext_cli_placed_ok setUnackKyberId_cli_placed_ok setUnackPreKeyMsg_cli_placed_ok
   spqrChainParams_cli_placed_ok spqrInitialStateInnerSpec verifySignatureInnerSpec
   withReceiverChain_cli_placed_ok withSenderChain_cli_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecPlacedBudget
  (cliInitiate_slotOk_placed subroutine_ok_semInitSlot_of_noAllocFail)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
  (initEntryMemPlaced initiate_stage1_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
  (Stage2PlacedOk coinsFill_placed_ok_at_init_vmPreserved stage2Placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysPlacedBudget
  (stage3Dh1UnwindEvents stage3Dh2UnwindEvents stage3Dh3UnwindEvents stage3Dh4Opt
   stage3Dh4UnwindEvents stage3OkEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3PlacedBudget
  (initiate_stage3_okEvents_no_coins_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget
  (initiate_stage4_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget
  (initiate_stage5_placed_ok_with_panic)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced InitStoreCalleesPlaced
   initStoreCallees_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostSpqrAllocHooks)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (dirGetSpecPlaced dirPutSpecPlaced dirPutStrSpecPlaced readFileSpecPlaced
   sessDeserializeSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
  (idSavePoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSaveShimPlacedBudget
  (idSaveShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (idTrustPoll_placed_ok_of_deps identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustShimPlacedBudget
  (idTrustShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollPlacedBudget
  (sessLoadPoll_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadShimPlacedBudget
  (sessLoadShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
  (sessStoreShim_placed_ok_of_deps)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.AgreeBudget (calculateAgreement_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok_of_contracts subroutine_ok_createChainSpecX_of_createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec)
open VerifiedLibraries (mallocngLib)

/-! ## 1. Target `CliInitSlotOkPlacedAt` Predicate -/

/-- `initiate` slot contract at hook map `H` on Block 579 (`lsProg_579 H`) calling Block 521. -/
def CliInitSlotOkPlacedAt [LibsignalPlacement] {M : AllocCostModel}
    (H : LibsignalHooks) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) : Prop :=
  ∀ (S : RunSem) (sEnvs : RunSlotEnvs) (needs : RunNeeds),
    sEnvs.initiate = InitEnv →
    S.filesOk = filesOk₀ scopeIn (fun _ => True) →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
    needs.initiate = cliInitiateNeed cliRunBudgets →
    (slotsOfPlaced A lim sEnvs S needs).initiate.OkPlaced
      (lsProg_579 H) (lsmpl.base 521)

/-! ## 2. Unconditional Append-Delta Non-`allocFailedEvent` (`HookNoAllocFailed`) -/

/-- Append-delta trace invariant: `f s` only extends `s.trace` by a suffix `d` free of
`allocFailedEvent` (independent of whether `s.trace` already contains `allocFailedEvent`). -/
def TraceDeltaNoAllocFailed (s s' : State) : Prop :=
  ∃ d : List TraceEvent, s'.trace = s.trace ++ d ∧ allocFailedEvent ∉ d

/-- A hook `f` satisfies `HookNoAllocFailed` when every input state `s` steps to an append-delta
extension free of `allocFailedEvent`. -/
def HookNoAllocFailed (f : State → State) : Prop :=
  ∀ s : State, TraceDeltaNoAllocFailed s (f s)

/-- Every hooked function in `ext` satisfies `HookNoAllocFailed`. -/
def ExternNoAllocFailed (ext : String → Option (State → State)) : Prop :=
  ∀ name f, ext name = some f → HookNoAllocFailed f

theorem traceDeltaNoAllocFailed_refl (s : State) : TraceDeltaNoAllocFailed s s :=
  ⟨[], by simp⟩

theorem traceDeltaNoAllocFailed_of_eq {s s' : State} (h : s'.trace = s.trace) :
    TraceDeltaNoAllocFailed s s' :=
  ⟨[], by simp [h]⟩

theorem traceDeltaNoAllocFailed_trans {s0 s1 s2 : State}
    (h01 : TraceDeltaNoAllocFailed s0 s1) (h12 : TraceDeltaNoAllocFailed s1 s2) :
    TraceDeltaNoAllocFailed s0 s2 := by
  rcases h01 with ⟨d1, hd1, hn1⟩
  rcases h12 with ⟨d2, hd2, hn2⟩
  refine ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc], ?_⟩
  rw [List.mem_append, not_or]
  exact ⟨hn1, hn2⟩

theorem hookNoAllocFailed_of_trace_eq (f : State → State) (h : ∀ s, (f s).trace = s.trace) :
    HookNoAllocFailed f :=
  fun s => traceDeltaNoAllocFailed_of_eq (h s)

theorem externNoAllocFailed_none : ExternNoAllocFailed (fun _ => none) := by
  intro _ _ h
  cases h

private theorem not_mem_ofBytes (strm : OutputStream) (bs : List (BitVec 8)) :
    allocFailedEvent ∉ TraceEvent.ofBytes strm bs := by
  simp [TraceEvent.ofBytes, allocFailedEvent]

private theorem not_mem_fileChanged (p : String) :
    allocFailedEvent ∉ [TraceEvent.fileChanged p] := by
  simp [allocFailedEvent]

private theorem traceDelta_of_ofBytes {s s' : State} {strm : OutputStream} {bs : List (BitVec 8)}
    (h : s'.trace = s.trace ++ TraceEvent.ofBytes strm bs) :
    TraceDeltaNoAllocFailed s s' :=
  ⟨TraceEvent.ofBytes strm bs, h, not_mem_ofBytes strm bs⟩

private theorem traceDelta_of_fileChanged {s s' : State} {p : String}
    (h : s'.trace = s.trace ++ [TraceEvent.fileChanged p]) :
    TraceDeltaNoAllocFailed s s' :=
  ⟨[TraceEvent.fileChanged p], h, not_mem_fileChanged p⟩

private theorem tr_advancePC (s : State) : s.advancePC.trace = s.trace := rfl
private theorem tr_setPC (s : State) (x : BitVec 64) : (s.setPC x).trace = s.trace := rfl
private theorem tr_setPState (s : State) (x : PState) : (s.setPState x).trace = s.trace := rfl
private theorem tr_setMem (s : State) (m : Memory) : (s.setMem m).trace = s.trace := rfl
private theorem tr_setFpsr (s : State) (x : BitVec 32) : (s.setFpsr x).trace = s.trace := rfl
private theorem tr_orFpsr (s : State) (x : BitVec 32) : (s.orFpsr x).trace = s.trace := rfl
private theorem tr_setBrk (s : State) (x : BitVec 64) : (s.setBrk x).trace = s.trace := rfl
private theorem tr_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).trace = s.trace := rfl
private theorem tr_setFs (s : State) (x : FsState) : (s.setFs x).trace = s.trace := rfl
private theorem tr_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).trace = s.trace := rfl
private theorem tr_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).trace = s.trace := rfl
private theorem tr_appendTrace (s : State) (x : List TraceEvent) :
    (s.appendTrace x).trace = s.trace ++ x := rfl
private theorem tr_nextOracle (s : State) : s.nextOracle.trace = s.trace := rfl
private theorem tr_stepExclOracle (s : State) : s.stepExclOracle.trace = s.trace := rfl
private theorem tr_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by unfold State.writeReg64; split <;> rfl
private theorem tr_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := tr_writeReg64 s r (BitVec.zeroExtend 64 v)
private theorem tr_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by
  cases w
  · exact tr_writeReg32 s r (v.truncate 32)
  · exact tr_writeReg64 s r v
private theorem tr_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).trace = s.trace := rfl
private theorem tr_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).trace = s.trace := rfl
private theorem tr_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).trace = s.trace := rfl
private theorem tr_setStatus (s : State) (x : ExecStatus) : (s.setStatus x).trace = s.trace := rfl
private theorem retHook_trace (f : State → State) (s : State) :
    (retHook f s).trace = (f s).trace := rfl
private theorem returnToLinkRegister_trace (s : State) :
    (returnToLinkRegister s).trace = s.trace := rfl
private theorem restoreCallerRegs_trace (sCaller sCallee : State) :
    (restoreCallerRegs sCaller sCallee).trace = sCallee.trace := rfl
private theorem rustPanicked_trace (s : State) :
    (Rust.panicked s).trace = s.trace := rfl
private theorem unitResult_trace (ok : Bool) (s : State) :
    (unitResult ok s).trace = s.trace := by
  unfold unitResult
  rw [retHook_trace, tr_writeReg64]

local macro "trace_delta_close" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in
   repeat' split
   repeat' split
   all_goals
     try dsimp (config := { zeta := true, zetaHave := true }) only
     try simp only [tr_advancePC, tr_setPC, tr_setPState, tr_setMem, tr_setFpsr, tr_orFpsr,
       tr_setBrk, tr_setPhysMemAvail, tr_setFs, tr_setSigAction, tr_setSigAltStack,
       tr_nextOracle, tr_stepExclOracle, tr_appendTrace, tr_writeReg64, tr_writeReg32,
       tr_writeReg, tr_writeVReg128, tr_writeVReg64, tr_writeVReg32, tr_setStatus,
       retHook_trace, returnToLinkRegister_trace, restoreCallerRegs_trace, rustPanicked_trace,
       unitResult_trace]
     first
       | exact traceDeltaNoAllocFailed_of_eq rfl
       | exact traceDelta_of_ofBytes rfl
       | exact traceDelta_of_fileChanged rfl))

private theorem noAllocFailed_execIoctl : HookNoAllocFailed execIoctl := by
  intro s; dsimp (config := { zetaHave := true }) only [execIoctl]; trace_delta_close
private theorem noAllocFailed_execFcntl : HookNoAllocFailed execFcntl := by
  intro s; dsimp (config := { zetaHave := true }) only [execFcntl]; trace_delta_close
private theorem noAllocFailed_execClose : HookNoAllocFailed execClose := by
  intro s; dsimp (config := { zetaHave := true }) only [execClose]; trace_delta_close
private theorem noAllocFailed_execLseek : HookNoAllocFailed execLseek := by
  intro s; dsimp (config := { zetaHave := true }) only [execLseek]; trace_delta_close
private theorem noAllocFailed_execReadCommon (b : Bool) :
    HookNoAllocFailed (fun s => execReadCommon s b) := by
  intro s; dsimp (config := { zetaHave := true }) only [execReadCommon]; trace_delta_close
private theorem noAllocFailed_execFstat : HookNoAllocFailed execFstat := by
  intro s; dsimp (config := { zetaHave := true }) only [execFstat]; trace_delta_close
private theorem noAllocFailed_execPpoll : HookNoAllocFailed execPpoll := by
  intro s
  dsimp (config := { zetaHave := true }) only [execPpoll]
  by_cases h1 : (s.readReg64 Reg.x2 == 0#64) = true
  · simp only [h1, ↓reduceIte]; exact traceDeltaNoAllocFailed_of_eq rfl
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (!decide ((s.readReg64 Reg.x2).toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm Option.r (s.readReg64 Reg.x2) 16) = true
  · simp only [h2, ↓reduceIte]; exact traceDeltaNoAllocFailed_of_eq rfl
  simp only [eq_false h2, ↓reduceIte]
  by_cases h3 : (!s.mem.canRead (s.readReg64 Reg.x2) 16) = true
  · simp only [h3, ↓reduceIte]; exact traceDeltaNoAllocFailed_of_eq rfl
  simp only [eq_false h3, ↓reduceIte]
  by_cases h4 : ((s.mem.read64 (s.readReg64 Reg.x2)).slt 0#64 || (s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).slt 0#64 || !decide ((s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).toNat < 1000000000)) = true
  · simp only [h4, ↓reduceIte]; exact traceDeltaNoAllocFailed_of_eq rfl
  simp only [eq_false h4, ↓reduceIte]
  trace_delta_close
private theorem noAllocFailed_execSetTidAddress : HookNoAllocFailed execSetTidAddress :=
  fun _ => traceDeltaNoAllocFailed_of_eq rfl
private theorem noAllocFailed_execSchedGetaffinity : HookNoAllocFailed execSchedGetaffinity := by
  intro s; dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; trace_delta_close
private theorem noAllocFailed_execClockGettime : HookNoAllocFailed execClockGettime := by
  intro s; dsimp (config := { zetaHave := true }) only [execClockGettime]; trace_delta_close
private theorem noAllocFailed_execMmap : HookNoAllocFailed execMmap := by
  intro s; dsimp (config := { zetaHave := true }) only [execMmap]; trace_delta_close
private theorem noAllocFailed_execBrk : HookNoAllocFailed execBrk := by
  intro s; dsimp (config := { zetaHave := true }) only [execBrk]; trace_delta_close
private theorem noAllocFailed_execMunmap : HookNoAllocFailed execMunmap := by
  intro s; dsimp (config := { zetaHave := true }) only [execMunmap]; trace_delta_close
private theorem noAllocFailed_execMremap : HookNoAllocFailed execMremap := by
  intro s; dsimp (config := { zetaHave := true }) only [execMremap]; trace_delta_close
private theorem noAllocFailed_execMprotect : HookNoAllocFailed execMprotect := by
  intro s; dsimp (config := { zetaHave := true }) only [execMprotect]; trace_delta_close
private theorem noAllocFailed_execMadvise : HookNoAllocFailed execMadvise := by
  intro s; dsimp (config := { zetaHave := true }) only [execMadvise]; trace_delta_close
private theorem noAllocFailed_execGetrandom : HookNoAllocFailed execGetrandom := by
  intro s; dsimp (config := { zetaHave := true }) only [execGetrandom]; trace_delta_close
private theorem noAllocFailed_execGetpid : HookNoAllocFailed execGetpid :=
  fun _ => traceDeltaNoAllocFailed_of_eq rfl
private theorem noAllocFailed_execRtSigprocmask : HookNoAllocFailed execRtSigprocmask := by
  intro s; dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; trace_delta_close
private theorem noAllocFailed_execSigaltstack : HookNoAllocFailed execSigaltstack := by
  intro s; dsimp (config := { zetaHave := true }) only [execSigaltstack]; trace_delta_close
private theorem noAllocFailed_execRtSigaction : HookNoAllocFailed execRtSigaction := by
  intro s; dsimp (config := { zetaHave := true }) only [execRtSigaction]; trace_delta_close
private theorem noAllocFailed_execTkill : HookNoAllocFailed execTkill := by
  intro s; dsimp (config := { zetaHave := true }) only [execTkill]; trace_delta_close
private theorem noAllocFailed_execTgkill : HookNoAllocFailed execTgkill := by
  intro s; dsimp (config := { zetaHave := true }) only [execTgkill]; trace_delta_close

private theorem noAllocFailed_openatPure (s : State) (dfd : BitVec 32) (rawPath : String)
    (flags mode : BitVec 32) :
    TraceDeltaNoAllocFailed s (applyOpenVerdict s (openatPure s.fs dfd rawPath flags mode)) := by
  dsimp (config := { zetaHave := true }) only [openatPure]
  cases hchk : checkOpenFlags flags with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact traceDeltaNoAllocFailed_of_eq rfl
  | none =>
    dsimp only
    generalize s.fs.allocFd = fd?
    (repeat' split) <;> dsimp only [applyOpenVerdict] <;> (repeat' split)
    all_goals first
      | exact traceDeltaNoAllocFailed_of_eq rfl
      | exact traceDelta_of_fileChanged rfl

private theorem noAllocFailed_execOpenat : HookNoAllocFailed execOpenat := by
  intro s
  dsimp (config := { zetaHave := true }) only [execOpenat]
  cases hchk : checkOpenFlags (s.readReg32 Reg.x2) with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact traceDeltaNoAllocFailed_of_eq rfl
  | none =>
    cases readCString s.mem (s.readReg64 Reg.x1) with
    | trap _ => exact traceDeltaNoAllocFailed_of_eq rfl
    | errno _ => exact traceDeltaNoAllocFailed_of_eq rfl
    | ok rawPath => exact noAllocFailed_openatPure s _ rawPath _ _

private theorem ite_traceDelta {c : Prop} [inst : Decidable c] {s a b : State}
    (ha : TraceDeltaNoAllocFailed s a) (hb : TraceDeltaNoAllocFailed s b) :
    TraceDeltaNoAllocFailed s (if c then a else b) := by
  cases inst with
  | isFalse _ => exact hb
  | isTrue _ => exact ha

private theorem noAllocFailed_execWrite : HookNoAllocFailed execWrite := by
  intro s
  dsimp (config := { zetaHave := true }) only [execWrite]
  by_cases h1 : (s.readReg32 Reg.x0).slt 0#32 = true
  · simp only [h1, ↓reduceIte]; exact traceDeltaNoAllocFailed_of_eq rfl
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (BitVec.zeroExtend 64 (s.readReg32 Reg.x0) == 1#64 || BitVec.zeroExtend 64 (s.readReg32 Reg.x0) == 2#64) = true
  · simp only [h2, ↓reduceIte]; trace_delta_close
  simp only [eq_false h2, ↓reduceIte]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
    (dsimp only; repeat' apply ite_traceDelta; all_goals trace_delta_close)

private theorem standardEntry_noAllocFailed :
    ∀ p ∈ Syscall.standardTable, HookNoAllocFailed p.2 := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact noAllocFailed_execReadCommon false
  · exact noAllocFailed_execWrite
  · exact fun s =>
      LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_traceDeltaFree
        (noAllocFailed_execReadCommon false) s
  · exact fun s =>
      LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_traceDeltaFree
        noAllocFailed_execWrite s
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact noAllocFailed_execFcntl
  · exact noAllocFailed_execIoctl
  · exact noAllocFailed_execOpenat
  · exact noAllocFailed_execClose
  · exact noAllocFailed_execLseek
  · exact noAllocFailed_execReadCommon true
  · exact noAllocFailed_execFstat
  · exact noAllocFailed_execPpoll
  · exact noAllocFailed_execBrk
  · exact noAllocFailed_execMunmap
  · exact noAllocFailed_execMremap
  · exact noAllocFailed_execMmap
  · exact noAllocFailed_execMprotect
  · exact noAllocFailed_execMadvise
  · exact noAllocFailed_execTkill
  · exact noAllocFailed_execTgkill
  · exact noAllocFailed_execSigaltstack
  · exact noAllocFailed_execRtSigaction
  · exact noAllocFailed_execRtSigprocmask
  · exact noAllocFailed_execClockGettime
  · exact noAllocFailed_execGetrandom
  · exact noAllocFailed_execSetTidAddress
  · exact noAllocFailed_execSchedGetaffinity
  · exact noAllocFailed_execGetpid
  · exact noAllocFailed_execGetpid

/-- `Syscall.standard` (`execSyscall`) satisfies `HookNoAllocFailed`. -/
theorem execSyscall_noAllocFailed : HookNoAllocFailed execSyscall := by
  intro s
  change TraceDeltaNoAllocFailed s (Syscall.dispatch Syscall.standardTable s)
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact standardEntry_noAllocFailed (nr, fn) (List.mem_of_find?_eq_some h) s
  · exact traceDeltaNoAllocFailed_of_eq rfl

private theorem evalInst_eq_execInst_of_ne_svc0 (prog : Program) (inst : Instr) (s : State)
    (his : inst ≠ .system false 0#16) : prog.evalInst inst s = execInst inst s := by
  cases inst <;> try rfl
  rename_i isHalt imm
  cases isHalt
  · by_cases h0 : imm = 0#16
    · exact absurd (h0 ▸ rfl) his
    · simp [Program.evalInst, execInstWithSvc, execInst, h0]
  · rfl

/-- One `Step prog` satisfies `TraceDeltaNoAllocFailed` when `prog.svc` and all `prog.externAt?`
hooks satisfy `HookNoAllocFailed`. -/
theorem step_traceDeltaNoAllocFailed {prog : Program}
    (hsvc : HookNoAllocFailed prog.svc)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookNoAllocFailed f)
    {s s' : State} (h : Step prog s s') :
    TraceDeltaNoAllocFailed s s' := by
  cases h with
  | @exec inst _ _ =>
    by_cases his : inst = .system false 0#16
    · subst his
      exact hsvc s
    · rw [evalInst_eq_execInst_of_ne_svc0 prog inst s his]
      exact traceDeltaNoAllocFailed_of_eq (execInst_trace_of_ne_svc0 inst s his)
  | halt_unmapped _ _ _ => exact traceDeltaNoAllocFailed_of_eq rfl
  | extern _ hext _ _ => exact hhooks _ _ hext s
  | extern_fault _ _ _ => exact traceDeltaNoAllocFailed_of_eq rfl

/-- Multi-step `Steps prog` preserves `TraceDeltaNoAllocFailed`. -/
theorem steps_traceDeltaNoAllocFailed {prog : Program}
    (hsvc : HookNoAllocFailed prog.svc)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookNoAllocFailed f)
    {s s' : State} (h : Steps prog s s') :
    TraceDeltaNoAllocFailed s s' := by
  induction h with
  | refl _ => exact traceDeltaNoAllocFailed_refl _
  | step h1 _ ih =>
    exact traceDeltaNoAllocFailed_trans (step_traceDeltaNoAllocFailed hsvc hhooks h1) ih

private theorem findSome_noAllocFailed (F : String → Option (State → State))
    (hF : ExternNoAllocFailed F) (off : Nat) :
    ∀ (l : List (String × Nat)) (f : State → State),
      (l.findSome? fun (n, o) => if o == off then F n else none) = some f →
      HookNoAllocFailed f
  | [], _, h => nomatch h
  | (n, o) :: tl, f, h => by
    simp only [List.findSome?_cons] at h
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h
      cases hfn : F n with
      | some fn =>
        rw [hfn] at h
        simp only [Option.some.injEq] at h
        subst h
        exact hF n fn hfn
      | none =>
        rw [hfn] at h
        exact findSome_noAllocFailed F hF off tl f h
    · simp only [eq_false ho, ↓reduceIte] at h
      exact findSome_noAllocFailed F hF off tl f h

theorem externAt_noAllocFailed_of_externs {prog : Program}
    (hov : ExternNoAllocFailed prog.overrides)
    (hext : ExternNoAllocFailed prog.externs) :
    ∀ pc f, prog.externAt? pc = some f → HookNoAllocFailed f := by
  intro pc f he
  unfold Program.externAt? Program.hookAtOff? at he
  cases h1 : (prog.stubs.findSome? fun (n, o) =>
      if o == (pc - prog.base).toNat then prog.externs n else none) with
  | some f1 =>
    rw [h1] at he
    dsimp only [Option.or] at he
    injection he with he
    subst he
    exact findSome_noAllocFailed prog.externs hext (pc - prog.base).toNat prog.stubs f1 h1
  | none =>
    rw [h1] at he
    simp only [Option.none_or] at he
    exact findSome_noAllocFailed prog.overrides hov (pc - prog.base).toNat prog.symbols f he

private theorem multiCodeROHookEntry_trace
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat) (entry : BitVec 64)
    (s0 : State) :
    (multiCodeROHookEntry lib mpl i entry s0).trace = s0.trace := rfl

private theorem multiCodeROHookExit_trace
    (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement) (i : Nat) (s0 sf : State) :
    (multiCodeROHookExit lib mpl i s0 sf).trace = sf.trace := by
  unfold multiCodeROHookExit
  dsimp only
  split <;> rfl

/-- `MultiPlacedLib.codeROSubroutineHook` with `externs = none`, `overrides = none`, and
`svc = Syscall.standard` satisfies `HookNoAllocFailed`. -/
theorem codeROSubroutineHook_noAllocFailed (lib : Obj.MultiPlacedLib) (mpl : Obj.MultiPlacement)
    (fnName : String) :
    HookNoAllocFailed
      (lib.codeROSubroutineHook mpl fnName (fun _ => none) (fun _ => none) Syscall.standard) := by
  classical
  intro s0
  unfold Obj.MultiPlacedLib.codeROSubroutineHook
  cases Obj.lookupBlockSym fnName lib.blocks with
  | none => exact traceDeltaNoAllocFailed_refl s0
  | some p =>
    rcases p with ⟨i, off⟩
    dsimp only
    split
    · rename_i h
      let prog := lib.blockProgram mpl i (fun _ => none) (fun _ => none) Syscall.standard
      let s0' := multiCodeROHookEntry lib mpl i (lib.fnAddr mpl fnName) s0
      have h0 : TraceDeltaNoAllocFailed s0 s0' :=
        traceDeltaNoAllocFailed_of_eq (multiCodeROHookEntry_trace lib mpl i _ s0)
      have hsteps : Steps prog s0' (Classical.choose h) := (Classical.choose_spec h).1.toSteps
      have hov0 : ExternNoAllocFailed prog.overrides := by
        intro _ _ hg
        dsimp only [prog, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
          Program.rebase] at hg
        exact nomatch hg
      have hext0 : ExternNoAllocFailed prog.externs := by
        intro _ _ hg
        dsimp only [prog, Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program,
          Program.rebase] at hg
        exact nomatch hg
      have hno : ∀ pc f, prog.externAt? pc = some f → HookNoAllocFailed f :=
        externAt_noAllocFailed_of_externs hov0 hext0
      have htr : TraceDeltaNoAllocFailed s0' (Classical.choose h) :=
        steps_traceDeltaNoAllocFailed execSyscall_noAllocFailed hno hsteps
      have hexit : TraceDeltaNoAllocFailed (Classical.choose h)
          (multiCodeROHookExit lib mpl i s0 (Classical.choose h)) :=
        traceDeltaNoAllocFailed_of_eq (multiCodeROHookExit_trace lib mpl i s0 _)
      exact traceDeltaNoAllocFailed_trans (traceDeltaNoAllocFailed_trans h0 htr) hexit
    · exact traceDeltaNoAllocFailed_refl s0

theorem stepRustAlloc1_noAllocFailed (mpl : Obj.MultiPlacement) (zeroed : Bool)
    (frameBytes size : Nat) {k : State → BitVec 64 → State}
    (hk : ∀ t p, TraceDeltaNoAllocFailed t (k t p)) :
    HookNoAllocFailed (stepRustAlloc1 mpl zeroed frameBytes size k) := by
  intro s
  cases zeroed with
  | false =>
    unfold stepRustAlloc1
    simp only [Bool.false_eq_true, ↓reduceIte]
    let spCall := s.sp - BitVec.ofNat 64 frameBytes
    let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)
    have hsCall : TraceDeltaNoAllocFailed s sCall := by
      dsimp only [sCall]; rw [TraceDeltaNoAllocFailed]; refine ⟨[], ?_, by simp⟩
      rw [tr_writeReg64, tr_writeReg64, List.append_nil]
    have hs1 := codeROSubroutineHook_noAllocFailed mallocngLib mpl "malloc" sCall
    have hs01 := traceDeltaNoAllocFailed_trans hsCall hs1
    split
    · exact hs01
    · split
      · exact traceDeltaNoAllocFailed_trans hs01
          (traceDeltaNoAllocFailed_of_eq (by rw [rustPanicked_trace, restoreCallerRegs_trace]))
      · exact traceDeltaNoAllocFailed_trans
          (traceDeltaNoAllocFailed_trans hs01
            (traceDeltaNoAllocFailed_of_eq (restoreCallerRegs_trace _ _)))
          (hk _ _)
  | true =>
    unfold stepRustAlloc1
    simp only [↓reduceIte]
    let spCall := s.sp - BitVec.ofNat 64 frameBytes
    let sCall :=
      ((s.writeReg64 .sp spCall).writeReg64 .x0 (BitVec.ofNat 64 size)).writeReg64 .x1 1#64
    have hsCall : TraceDeltaNoAllocFailed s sCall := by
      dsimp only [sCall]; rw [TraceDeltaNoAllocFailed]; refine ⟨[], ?_, by simp⟩
      rw [tr_writeReg64, tr_writeReg64, tr_writeReg64, List.append_nil]
    have hs1 := codeROSubroutineHook_noAllocFailed mallocngLib mpl "calloc" sCall
    have hs01 := traceDeltaNoAllocFailed_trans hsCall hs1
    split
    · exact hs01
    · split
      · exact traceDeltaNoAllocFailed_trans hs01
          (traceDeltaNoAllocFailed_of_eq (by rw [rustPanicked_trace, restoreCallerRegs_trace]))
      · exact traceDeltaNoAllocFailed_trans
          (traceDeltaNoAllocFailed_trans hs01
            (traceDeltaNoAllocFailed_of_eq (restoreCallerRegs_trace _ _)))
          (hk _ _)

theorem stepRustDealloc1_noAllocFailed (mpl : Obj.MultiPlacement) (frameBytes : Nat)
    (ptr : BitVec 64) {k : State → State}
    (hk : HookNoAllocFailed k) :
    HookNoAllocFailed (stepRustDealloc1 mpl frameBytes ptr k) := by
  intro s
  unfold stepRustDealloc1
  dsimp only
  let spCall := s.sp - BitVec.ofNat 64 frameBytes
  let sCall := (s.writeReg64 .sp spCall).writeReg64 .x0 ptr
  have hsCall : TraceDeltaNoAllocFailed s sCall := by
    dsimp only [sCall]; rw [TraceDeltaNoAllocFailed]; refine ⟨[], ?_, by simp⟩
    rw [tr_writeReg64, tr_writeReg64, List.append_nil]
  have hs1 := codeROSubroutineHook_noAllocFailed mallocngLib mpl "free" sCall
  have hs01 := traceDeltaNoAllocFailed_trans hsCall hs1
  split
  · exact hs01
  · exact traceDeltaNoAllocFailed_trans
      (traceDeltaNoAllocFailed_trans hs01
        (traceDeltaNoAllocFailed_of_eq (restoreCallerRegs_trace _ _)))
      (hk _)

theorem aesEncHookMallocng_noAllocFailed (mpl : Obj.MultiPlacement)
    (E : AesKey → Block → Block) :
    HookNoAllocFailed (aesEncHookMallocng mpl E) := by
  intro s0
  unfold aesEncHookMallocng
  split
  · exact traceDeltaNoAllocFailed_of_eq rfl
  · dsimp only
    split
    · exact traceDeltaNoAllocFailed_of_eq rfl
    · refine stepRustAlloc1_noAllocFailed mpl true _ _ (fun _ _ => ?_) s0
      exact traceDeltaNoAllocFailed_of_eq (by rw [retHook_trace, tr_setMem])

theorem aesDecHookMallocng_noAllocFailed (mpl : Obj.MultiPlacement)
    (D : AesKey → Block → Block) :
    HookNoAllocFailed (aesDecHookMallocng mpl D) := by
  intro s0
  unfold aesDecHookMallocng
  split
  · exact traceDeltaNoAllocFailed_of_eq rfl
  · dsimp only
    split
    · exact traceDeltaNoAllocFailed_of_eq (by rw [retHook_trace, tr_setMem])
    · refine stepRustAlloc1_noAllocFailed mpl true _ _ (fun s1 p => ?_) s0
      split
      · exact traceDeltaNoAllocFailed_of_eq (by rw [retHook_trace, tr_setMem])
      · refine stepRustDealloc1_noAllocFailed mpl _ p (fun _ => ?_) s1
        exact traceDeltaNoAllocFailed_of_eq (by rw [retHook_trace, tr_setMem])

theorem libcruxHmacHookMallocng_noAllocFailed (mpl : Obj.MultiPlacement)
    (F : ShaState → List (BitVec 8) → ShaState) :
    HookNoAllocFailed (libcruxHmacHookMallocng mpl F) := by
  intro s0
  unfold libcruxHmacHookMallocng
  split
  · exact traceDeltaNoAllocFailed_of_eq rfl
  · dsimp only
    split
    · exact traceDeltaNoAllocFailed_of_eq rfl
    · refine stepRustAlloc1_noAllocFailed mpl true _ 64 (fun s1 pKey => ?_) s0
      refine stepRustAlloc1_noAllocFailed mpl false _ 64 (fun s2 pIpad => ?_) s1
      refine stepRustAlloc1_noAllocFailed mpl false _ 64 (fun s3 pOpad => ?_) s2
      refine stepRustDealloc1_noAllocFailed mpl _ pOpad (fun s4 => ?_) s3
      refine stepRustDealloc1_noAllocFailed mpl _ pIpad (fun s5 => ?_) s4
      refine stepRustDealloc1_noAllocFailed mpl _ pKey (fun s6 => ?_) s5
      refine stepRustAlloc1_noAllocFailed mpl false _ 32 (fun _ _ => ?_) s6
      exact traceDeltaNoAllocFailed_of_eq (by rw [retHook_trace, tr_setMem])

private theorem noAllocFailed_hookMemset : HookNoAllocFailed hookMemset := by
  intro s; unfold hookMemset; rw [TraceDeltaNoAllocFailed]
  refine ⟨[], ?_, by simp⟩
  rw [retHook_trace]; dsimp (config := { zetaHave := true }) only
  rw [tr_setMem, List.append_nil]

private theorem noAllocFailed_hookMemcpy : HookNoAllocFailed hookMemcpy := by
  intro s; unfold hookMemcpy; rw [TraceDeltaNoAllocFailed]
  refine ⟨[], ?_, by simp⟩
  rw [retHook_trace]; dsimp (config := { zetaHave := true }) only
  rw [tr_setMem, List.append_nil]

private theorem noAllocFailed_hookMemmove : HookNoAllocFailed hookMemmove :=
  noAllocFailed_hookMemcpy

private theorem noAllocFailed_cliBcmpHook
    (bcmp : List (BitVec 8) → List (BitVec 8) → BitVec 64) :
    HookNoAllocFailed (cliBcmpHook bcmp) := by
  intro s; unfold cliBcmpHook; trace_delta_close

private theorem noAllocFailed_strlenHook : HookNoAllocFailed strlenHook := by
  intro s; unfold strlenHook; dsimp only; trace_delta_close

private theorem noAllocFailed_writeFileHook : HookNoAllocFailed writeFileHook := by
  intro s; unfold writeFileHook; dsimp only; trace_delta_close

private theorem noAllocFailed_writeStdoutHook : HookNoAllocFailed writeStdoutHook := by
  intro s; unfold writeStdoutHook; dsimp only; trace_delta_close

private theorem noAllocFailed_memrchrHook : HookNoAllocFailed memrchrHook := by
  intro s; unfold memrchrHook; dsimp only; trace_delta_close

private theorem noAllocFailed_fromUtf8Hook
    (err : List (BitVec 8) → BitVec 64 × BitVec 16) :
    HookNoAllocFailed (fromUtf8Hook err) := by
  intro s; unfold fromUtf8Hook; dsimp only; trace_delta_close

private theorem noAllocFailed_fmtWriteHook0 : HookNoAllocFailed fmtWriteHook0 := by
  intro s; unfold fmtWriteHook0; trace_delta_close

private theorem noAllocFailed_durationSinceExactHook : HookNoAllocFailed durationSinceExactHook := by
  intro s; unfold durationSinceExactHook; dsimp only; trace_delta_close

private theorem noAllocFailed_timeAddHook : HookNoAllocFailed timeAddHook := by
  intro s; unfold timeAddHook; dsimp only; trace_delta_close

private theorem noAllocFailed_blackBoxHook : HookNoAllocFailed blackBoxHook := by
  intro s; unfold blackBoxHook; trace_delta_close

private theorem noAllocFailed_torsionFreeHook (Q : PqxdhPrims) :
    HookNoAllocFailed (torsionFreeHook Q.isTorsionFree) := by
  intro s; unfold torsionFreeHook; trace_delta_close

private theorem noAllocFailed_mlkemPk1Hook : HookNoAllocFailed mlkemPk1Hook := by
  intro s; unfold mlkemPk1Hook; trace_delta_close

private theorem noAllocFailed_mlkemPk2Hook : HookNoAllocFailed mlkemPk2Hook := by
  intro s; unfold mlkemPk2Hook; trace_delta_close

private theorem noAllocFailed_mlkemValidatePkHook (Q : PqxdhPrims) :
    HookNoAllocFailed (mlkemValidatePkHook Q.K) := by
  intro s; unfold mlkemValidatePkHook; trace_delta_close

theorem externNoAllocFailed_of_table {tbl : List (String × (State → State))}
    (htbl : ∀ p ∈ tbl, HookNoAllocFailed p.2) :
    ExternNoAllocFailed (fun name => tbl.lookup name) := by
  intro name f hlook
  dsimp only at hlook
  induction tbl with
  | nil => simp at hlook
  | cons hd tl ih =>
    rcases hd with ⟨k, g⟩
    simp only [List.lookup] at hlook
    cases hbeq : (name == k) with
    | true =>
      rw [hbeq] at hlook
      injection hlook with hgf
      subst hgf
      exact htbl (k, g) (List.Mem.head tl)
    | false =>
      rw [hbeq] at hlook
      exact ih (fun p hp => htbl p (List.Mem.tail _ hp)) hlook

private theorem tableNoAllocFailed_cliPqxdhPlaced (mmpl : Obj.MultiPlacement)
    (C : Crypto) (Q : PqxdhPrims) :
    ∀ p ∈ cliPqxdhHookTablePlaced mmpl C Q, HookNoAllocFailed p.2 := by
  simp only [cliPqxdhHookTablePlaced, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact noAllocFailed_torsionFreeHook Q
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact noAllocFailed_mlkemPk1Hook
  · exact noAllocFailed_mlkemPk2Hook
  · exact fun s => traceDeltaNoAllocFailed_of_eq
      (by dsimp only [mlkemEncaps1Hook]; rw [retHook_trace]; split <;> rfl)
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact noAllocFailed_mlkemValidatePkHook Q
  · exact libcruxHmacHookMallocng_noAllocFailed mmpl C.F

/-- Every row of `cliHookTablePlaced mmpl W` satisfies `HookNoAllocFailed`. -/
theorem tableNoAllocFailed_cliHookTablePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, HookNoAllocFailed p.2 := by
  intro p hp
  unfold cliHookTablePlaced at hp
  rw [List.mem_append] at hp
  rcases hp with hpq | hcli
  · exact tableNoAllocFailed_cliPqxdhPlaced mmpl W.C W.Q p hpq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcli
    rcases hcli with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact noAllocFailed_hookMemmove
    · exact noAllocFailed_cliBcmpHook W.bcmp
    · exact noAllocFailed_strlenHook
    · exact noAllocFailed_writeFileHook
    · exact noAllocFailed_writeStdoutHook
    · exact noAllocFailed_memrchrHook
    · exact noAllocFailed_fromUtf8Hook W.utf8Err
    · exact noAllocFailed_fmtWriteHook0
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
    · exact noAllocFailed_durationSinceExactHook
    · exact noAllocFailed_timeAddHook
    · exact noAllocFailed_blackBoxHook
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
    · exact aesEncHookMallocng_noAllocFailed mmpl W.C.E
    · exact aesDecHookMallocng_noAllocFailed mmpl W.C.D
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
    · exact fun _ => traceDeltaNoAllocFailed_of_eq rfl

/-- Every hook in `cliExternsPlaced mmpl W` satisfies `HookNoAllocFailed`. -/
theorem externNoAllocFailed_cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ExternNoAllocFailed (cliExternsPlaced mmpl W) := by
  intro name f h
  unfold cliExternsPlaced at h
  split at h
  · injection h with hrf
    subst hrf
    exact fun _ => traceDeltaNoAllocFailed_of_eq rfl
  · exact externNoAllocFailed_of_table (tableNoAllocFailed_cliHookTablePlaced mmpl W) name f h

/-- Any symbol resolved by `cliGhostExterns gh baseExt` comes either from `gh`'s own overlay
(`cliGhostExterns gh (fun _ => none)`) or from `baseExt`. -/
theorem cliGhostExterns_mem_or_base (gh : CliGhostHooks) (baseExt : LibsignalHooks)
    (sym : String) (f : State → State)
    (h : cliGhostExterns gh baseExt sym = some f) :
    cliGhostExterns gh (fun _ => none) sym = some f ∨ baseExt sym = some f := by
  unfold cliGhostExterns at h ⊢
  repeat' split
  all_goals simp_all

/-- Overlaying `gh : CliGhostHooks` onto `baseExt` preserves `ExternNoAllocFailed` whenever `gh`'s
own hooks (`cliGhostExterns gh (fun _ => none)`) satisfy `ExternNoAllocFailed`. -/
theorem externNoAllocFailed_cliGhostExterns {gh : CliGhostHooks} {baseExt : LibsignalHooks}
    (hgh : ExternNoAllocFailed (cliGhostExterns gh (fun _ => none)))
    (hbase : ExternNoAllocFailed baseExt) :
    ExternNoAllocFailed (cliGhostExterns gh baseExt) := by
  intro sym f h
  rcases cliGhostExterns_mem_or_base gh baseExt sym f h with h1 | h2
  · exact hgh sym f h1
  · exact hbase sym f h2

/-- Append-delta non-`allocFailedEvent` unconditionally refutes `allocFailedIn s0 sf`
without constraining `s0.trace`. -/
theorem not_allocFailedIn_of_traceDelta {s0 sf : State}
    (hd : TraceDeltaNoAllocFailed s0 sf) :
    ¬ allocFailedIn s0 sf := by
  rcases hd with ⟨d, htr, hnd⟩
  unfold allocFailedIn
  rw [htr, List.drop_left]
  exact hnd

/-- Every `IsLsBlockProg prog i ext` run under `ExternNoAllocFailed ext` satisfies
`¬ allocFailedIn s0 sf` unconditionally. -/
theorem lsProg_not_allocFailedIn_of_externs [LibsignalPlacement]
    {ext : LibsignalHooks} (hext : ExternNoAllocFailed ext)
    {prog : Program} {i : Nat} [hprog : IsLsBlockProg prog i ext]
    (s0 sf : State) (hsteps : Steps prog s0 sf) :
    ¬ allocFailedIn s0 sf := by
  rw [hprog.eq_blockProgram] at hsteps
  have hov0 : ExternNoAllocFailed
      (CryptoVerification.libsignalSessionLib.blockProgram lsmpl i ext).overrides := by
    intro _ _ hg
    dsimp only [Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program, Program.rebase] at hg
    exact nomatch hg
  have hext0 : ExternNoAllocFailed
      (CryptoVerification.libsignalSessionLib.blockProgram lsmpl i ext).externs := by
    intro sym f hg
    dsimp only [Obj.MultiPlacedLib.blockProgram, Obj.PlacedLib.program, Program.rebase] at hg
    exact hext sym f hg
  have hno : ∀ pc f,
      (CryptoVerification.libsignalSessionLib.blockProgram lsmpl i ext).externAt? pc = some f →
      HookNoAllocFailed f :=
    externAt_noAllocFailed_of_externs hov0 hext0
  have hsvc : (CryptoVerification.libsignalSessionLib.blockProgram lsmpl i ext).svc = execSyscall :=
    rfl
  exact not_allocFailedIn_of_traceDelta
    (steps_traceDeltaNoAllocFailed (hsvc ▸ execSyscall_noAllocFailed) hno hsteps)

/-- Every `IsLsBlockProg` at `cliGhostExterns gh' (cliExternsPlaced mmpl W)` never emits
`allocFailedIn s0 sf` whenever `gh'`'s ghost hooks satisfy `ExternNoAllocFailed`. -/
theorem lsProg_not_allocFailedIn_cliGhost [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (hgh : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    {prog : Program} {i : Nat}
    [IsLsBlockProg prog i (cliGhostExterns gh' (cliExternsPlaced mmpl W))]
    (s0 sf : State) (hsteps : Steps prog s0 sf) :
    ¬ allocFailedIn s0 sf :=
  lsProg_not_allocFailedIn_of_externs
    (externNoAllocFailed_cliGhostExterns hgh (externNoAllocFailed_cliExternsPlaced mmpl W))
    s0 sf hsteps

/-! ## 3. Minimal Parametric `W3GhostHooks` & W3 Store/Local Callee Instantiation -/

/-- Minimal `initiate` ghost-hook bundle on `cliGhostExterns gh' (cliExternsPlaced mmpl W)`,
parametric in `gh'` and single-`stk` `HookSat` on `lsReadFileSym`. -/
structure W3GhostHooks [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop) : Prop where
  alloc : CliGhostSpqrAllocHooks M A lim gh'
  strClone_fsT : ∀ f, gh'.stringClone = some f → HookFsTraced IsFsC f
  stringClone : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsStringCloneSym
    (stringCloneBudgetSpec M A lim)
  formatInner : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsFormatInnerSym
    (formatInnerBudgetSpec M A lim)
  readFile : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsReadFileSym
    (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)

/-- Lift `CliSlotCalleesInstPlacedBudgetSeams.CliSlotAllocHooks` to `W3GhostHooks` given the
single-`stk` `HookSat` on `lsReadFileSym`. -/
theorem W3GhostHooks.of_slotAllocHooks [LibsignalPlacement] {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {gh' : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hSlot : LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetSeams.CliSlotAllocHooks
      mmpl gh' W A lim ReadEnv)
    (hRead : HookSat (cliGhostExterns gh' (cliExternsPlaced mmpl W)) lsReadFileSym
      (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)) :
    W3GhostHooks mmpl gh' W A lim ReadEnv :=
  { alloc := hSlot.alloc
    strClone_fsT := hSlot.strClone_fsT
    stringClone := hSlot.stringClone
    formatInner := hSlot.formatInner
    readFile := hRead }

theorem skeletonHooks_of_w3GhostHooks [LibsignalPlacement] {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {gh' : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : W3GhostHooks mmpl gh' W A lim ReadEnv) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced.of_hooks
    mmpl gh' W hH.alloc hH.strClone_fsT hH.stringClone hH.formatInner

theorem initRunHooks_of_w3GhostHooks [LibsignalPlacement] {M : AllocCostModel}
    {mmpl : Obj.MultiPlacement} {gh' : CliGhostHooks} {W : CliHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    (hH : W3GhostHooks mmpl gh' W A lim ReadEnv) :
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced.of_hooks
    mmpl gh' W hH.alloc hH.strClone_fsT hH.stringClone hH.formatInner

private theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} :
    subroutine_ok prog (lsmpl.base 46)
      (sessDeserializeSpecPlaced (fun _ => False) A lim (fun _ _ => False)) := by
  refine subroutine_ok_outcome_intro fun ⟨_, _⟩ _ _ _ _ hpre _ => ?_
  obtain ⟨_, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessDeserializeSpecPlaced] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1 with ⟨_, _, _, hf, _⟩
  exact False.elim hf

/-- Discharges all 16 fields of `ExistingStoreCalleesPlaced` at `cliExistingStoreCalleesEnvs ReadEnv`
from `W3GhostHooks mmpl gh' W A lim ReadEnv` (using `hRead_withLsCodeRoLoaded_of_hookSat` at
`cliRunBudgets.readFile`). -/
theorem w3Exist_placed_ok_of_ghost [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (hH : W3GhostHooks mmpl gh' W A lim ReadEnv) :
    ExistingStoreCalleesPlaced A lim (cliExistingStoreCalleesEnvs ReadEnv)
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) cliRunBudgets := by
  let hh := skeletonHooks_of_w3GhostHooks hH
  let hh3 := initRunHooks_of_w3GhostHooks hH
  have hRead589 : subroutine_ok (lsProg_589 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
      (lsρ lsReadFileSym)
      (withLsCodeRoLoaded lsmpl
        (readFileSpecPlaced cliIo.rd cliWrOk A lim cliRunBudgets.readFile ReadEnv)) :=
    hRead_withLsCodeRoLoaded_of_hookSat
      (callerProg := lsProg_589 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
      (i := 589) (bi := 619) hH.readFile (by decide) (by decide)
  have hAddr := cliAddrText_placed_ok hh
  have hGet : subroutine_ok (lsProg_589 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A lim (DirGetEnv PathEnv ReadEnv cliIo.rd)
        cliRunBudgets.dirGetNeed) :=
    cliDirGet_placed_ok
      (readProg := lsProg_589 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (jRead := 589)
      (fun _ hp => hp.2) hh hRead589 (by decide) (by decide)
  have hPutStr : subroutine_ok (lsProg_543 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
      (lsmpl.base 543) (dirPutStrSpecPlaced A lim DirPutStrEnv cliDirPutStrNeedPlaced) :=
    dirPutStr_placed_ok_of_deps hh.alloc hh.panics hh.memcpyRO hh.bcmp
      (growProg := lsProg_586 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (jGrow := 586)
      (by decide) (by decide) (cliGrowOneDir_placed_ok hh.alloc hh.panics)
      (Nat.le_refl cliDirPutStrNeedPlaced)
  have hPut : subroutine_ok (lsProg_542 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
      (lsmpl.base 542) (dirPutSpecPlaced A lim DirPutEnv cliDirPutStk) :=
    dirPut_placed_caller_ok_of_deps
      (callerProg := lsProg_542 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (i := 542)
      hh.alloc hh.bcmp
      (growProg := lsProg_586 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (jGrow := 586)
      (by decide) (by decide) (cliGrowOneDir_placed_ok hh.alloc hh.panics)
      (Nat.le_refl dirPutNeedPlaced) (by decide)
  have hEq := publicKeyEq_placed_ok_of_bb (cliGhostExterns_blackBox_eq mmpl gh' W)
  have hDec := identityKey_decode_placed_ok (A := A) (cliGhostExterns gh' (cliExternsPlaced mmpl W))
  exact
    { dirGet := hGet
      addressText := hAddr
      dirPut := hPut
      idTrustShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idTrustShim_placed_ok_of_deps hh.alloc (by omega)
      idTrustPoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : extHookStack ≤ 65536 := by decide
        exact idTrustPoll_placed_ok_of_deps hh.alloc hGet hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      sessLoadShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x20 + extHookStack ≤ 516880 := by decide
        exact sessLoadShim_placed_ok_of_deps hh.alloc (by omega)
      sessLoadPoll := fun {stk} hstk =>
        sessLoadPoll_placed_ok_of_deps hh.alloc hAddr hGet
          (sessDeserialize_false_placed_ok
            (prog := lsProg_569 (cliGhostExterns gh' (cliExternsPlaced mmpl W))))
          (hh3.fs (prog := lsProg_569 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) (i := 569))
          (sessLoadPoll_stk_le (by decide) hstk)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      idSaveShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact idSaveShim_placed_ok_of_deps hh.alloc (by omega)
      idSavePoll := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have := stk_sub_ge_dirGet hstk
        have : cliDirPutStrNeedPlaced ≤ 65536 := by decide
        have : publicKeySerializeStackX ≤ 65536 := by decide
        have : extHookStack ≤ 65536 := by decide
        exact idSavePoll_placed_ok_of_deps hh.alloc hGet hPutStr hDec hEq (by omega)
          (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)
      sessStoreShim := fun {stk} hstk => by
        have := stk_sub_ge_base hstk
        have : 0x30 + extHookStack ≤ 516880 := by decide
        exact sessStoreShim_placed_ok_of_deps hh.alloc (by omega)
      rodata_idVt_keyPairSlot := rodata_cliIdentity_kpSlot_placed
      rodata_idVt_regIdSlot := rodata_cliIdentity_regIdSlot_placed
      rodata_idVt_saveSlot := rodata_cliIdentity_saveSlot_placed
      rodata_idVt_trustSlot := rodata_cliIdentity_trustSlot_placed
      rodata_sessVt_loadSlot := rodata_cliSession_loadSlot_placed
      rodata_sessVt_storeSlot := rodata_cliSession_storeSlot_placed }

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, noAllocShimSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem transfer_tr_codeRoLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns g (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl g W) entry (withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono hcallee
      (fun _ _ _ hp => by
        obtain ⟨hc, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl g W) hcrl (by decide) hj hj_unmut

private theorem hookSat_of_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (h : HookSat H sym spec.keepsFs) :
    HookSat H sym spec := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, hfn, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Arm64.Spec.keepsFs] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr hrest

private theorem hookSat_withStack_keepsFs {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hsat : HookSat H sym spec.keepsFs) (stk : Nat)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookSat H sym (withStack spec stk).keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  have hws := CryptoVerification.SignalSession.Cli.MainHops.hookOk_withStack hok stk hpan hex hoom
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hws x R s0 hrun hpre hsp with ⟨hkf, hsym, hout⟩
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan' | hex' | hoom'
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, Arm64.Spec.keepsFs] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan')
  · exact Or.inr (Or.inr (Or.inl hex'))
  · exact Or.inr (Or.inr (Or.inr hoom'))

private theorem createChain40_cro_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_40).base
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (createChainSpec M A lim W.C)) := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) := hh.hkdf
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (hookSat_of_keepsFs hh.memsetRegionKeepsFs)
  have hct207 := ct_eq_ro_placed_vm_ok_of_block
    (callerProg := (blkPC_207).rebase (blkPl_207).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    hh.blackBox (by decide)
  have hag40 := keys_ls_subroutine_ok_of_block_cro
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (calculateAgreement_placed_ok hh.dh hh.sharedDrop hct207
      (hookSat_noAllocShimBudget_of_withVmPreserved hh.shim) hh.rawAlloc hh.staticDrop)
  have hext40 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hexp40 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (cliGhostExterns g (cliExternsPlaced mmpl W))
  have hdealloc40 := keys_ls_hook_ok_of_mem
    (prog := (blkPC_40).rebase (blkPl_40).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (i := 40) hh.rawDealloc
  exact createChain_placed_ok_of_contracts (C := W.C) hag40 hext40 hexp40 hdealloc40

/-- Discharges all 19 fields of `InitLocalCalleesPlaced` from `Initiate.HooksPlacedBudget.RunHooksPlaced`
and the two W3-only seams (`spqrInitialState` on Block `327` and `verifySignature` on Block `203`). -/
theorem w3Local_placed_ok_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (mmpl : Obj.MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (B : RunBudgets)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (X : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩))))
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk := by
  have : HkdfPlacedHooksExactSat W.C.F (cliGhostExterns gh' (cliExternsPlaced mmpl W)) := hh.hkdf
  have : HkdfPlacedHooksExactBudgetSat W.C.F (cliGhostExterns gh' (cliExternsPlaced mmpl W)) :=
    HkdfPlacedHooksExactBudgetSat.of_exactSat (hookSat_of_keepsFs hh.memsetRegionKeepsFs)
  have hcc40 := createChain40_cro_placed_ok mmpl gh' W hh
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_placed_ok mmpl gh' W hh (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_placed_ok mmpl gh' W hh
      verifySignature := hVerifySig
      isSameAccount := w3IsSameAccount_placed_ok mmpl gh' A.repAlloc W
      calculateAgreement := calculateAgreement_cli_placed_ok mmpl gh' W hh
      derivePubKeyBytes := derivePubKeyBytes_cli_placed_ok mmpl gh' W hh
      handshakeDerive := fun X =>
        transfer_tr_codeRoLoaded
          (calleeProg := lsProg_59 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
          (handshakeKeysDerive_placed_ok
            (structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩)
            (pqxdhHkdfExtract_placed_ok_sat (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩))
            (pqxdhHkdfExpandMultiInfo_placed_ok_sat (primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)))
      kemCtSerialize := kemCtSerialize_cli_placed_ok mmpl gh' W hh
      rootKeyCreateChain := transfer_tr_codeRoLoaded
        (calleeProg := lsProg_40 (cliGhostExterns gh' (cliExternsPlaced mmpl W))) hcc40
      rootKeyCreateChainX := transfer_tr_codeRoLoaded
        (calleeProg := lsProg_40 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
        (subroutine_ok_createChainSpecX_of_createChainSpec hcc40)
      spqrChainParams := spqrChainParams_cli_placed_ok mmpl gh' W
      spqrInitialState := hSpqrInit
      sessionStateNew := sessionStateNew_cli_placed_ok mmpl gh' W hh
      withReceiverChain := withReceiverChain_cli_placed_ok mmpl gh' W hh
      withSenderChain := withSenderChain_cli_placed_ok mmpl gh' W hh
      setKyberCiphertext := setKyberCiphertext_cli_placed_ok mmpl gh' W
      setUnackPreKeyMsg := setUnackPreKeyMsg_cli_placed_ok mmpl gh' W hh
      setUnackKyberId := setUnackKyberId_cli_placed_ok mmpl gh' W
      promoteState := promoteState_cli_placed_ok mmpl gh' W hh }

/-! ## 4. Stage-3 `stage3OkEvents` Bundle & Block-`521` / Block-`579` Assembly -/

/-- Canonical Stage-3 budget-fitness & DH-unwind envelope predicate matching
`Stage3PlacedBudget.initiate_stage3_okEvents_no_coins_placed_ok`. -/
structure Stage3OkEventsFit {M : AllocCostModel} (lim : BudgetLimits)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (_ekASk _ekAPk : List (BitVec 8)) (_pqspkPtr : BitVec 64) (_opkId : BitVec 32)
    (_s0 : State) (st0 st : M.σ) : Prop where
  fitOk : FitsEvents M lim st (stage3OkEvents (stage3Dh4Opt X W kp be x.coins))
  envDh1 :
    (let P := modelPrims X ⟨W.C, W.Q⟩
     let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
     P.x25519 inp.ikASk inp.bundle.spkB = List.replicate 32 0) →
    ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh1UnwindEvents st = M.stepEvents evs st0
  envDh2 :
    (let P := modelPrims X ⟨W.C, W.Q⟩
     let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
     P.x25519 inp.ekASk inp.bundle.ikB = List.replicate 32 0) →
    ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh2UnwindEvents st = M.stepEvents evs st0
  envDh3 :
    (let P := modelPrims X ⟨W.C, W.Q⟩
     let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
     P.x25519 inp.ekASk inp.bundle.spkB = List.replicate 32 0) →
    ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh3UnwindEvents st = M.stepEvents evs st0
  envDh4 :
    (let P := modelPrims X ⟨W.C, W.Q⟩
     let inp := initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)
     SignalPqxdh.dhOptNonZero (inp.bundle.opkB?.map fun (_, opkPk) => P.x25519 inp.ekASk opkPk) =
       false) →
    ∃ evs, InitEnv x evs ∧ M.stepEvents stage3Dh4UnwindEvents st = M.stepEvents evs st0

/-- Canonical Stage-3 continuation event predicate (`evsS3 = stage3OkEvents ...`). -/
def Stage3OkEventsOut (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (_dk : SignalPqxdh.DRKey) (_hdr : SignalPqxdh.HandshakeHdr)
    (evsS3 : List AllocEvent) : Prop :=
  evsS3 = stage3OkEvents (stage3Dh4Opt X W kp be x.coins)

/-- Discharges `AssemblyPlacedBudget.Stage3PlacedOk` directly via
`Stage3PlacedBudget.initiate_stage3_okEvents_no_coins_placed_ok`. -/
theorem stage3PlacedOk_okEvents [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) :
    Stage3PlacedOk A lim InitStateEnv InitEnv
      (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X)
      mmpl gh' W X B S := by
  intro x st0 st be kp ekASk ekAPk pqspkPtr opkId stk s0 s3 Q Qp
    hh _hCoinsVm _hCoinsRoCl hLocal hFit hS hinitOk hcoinsLt hstk hstk64 hspk hs3
    hpost hpanic hnext
  exact initiate_stage3_okEvents_no_coins_placed_ok hh hLocal
    hFit.fitOk hFit.envDh1 hFit.envDh2 hFit.envDh3 hFit.envDh4
    hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpost hpanic
    fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr hs4 =>
      hnext s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr _
        (rfl : Stage3OkEventsOut W X x be kp dk hdr _) hs4

/-- Complete Block-`521` (`initProgPlaced mmpl gh' W`) budget-threaded assembly taking
`InitLocalCalleesPlaced` directly (without `SubsetA4InitCalleesPlaced`). -/
theorem cliInitiate_placed_ok_of_local [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) B)
    (hLocal : ∀ {stk : Nat}, cliInitiateNeed B ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh' W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh' W) initEntryPlaced
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
        A lim InitEnv S stk) := by
  have : CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InitTraceFsSound mmpl gh' W :=
    ⟨hh.fs⟩
  have hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh' W B stk :=
    initStoreCallees_placed_ok mmpl gh' W B hh hExist stk hstk hstk64
  have hLoc : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk :=
    hLocal hstk hstk64
  have hStage2 : Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh' W X B S :=
    stage2Placed_ok A lim eEnvs InitStateEnv InitEnv mmpl gh' W X B S
  have hCoinsRoCl : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsRoCl lsmpl
          (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget.coinsFillSpecPlacedW3 cStk)) :=
    fun hc1 hc2 => signal_session_coins_fill_placed_ok_at_init mmpl gh' W hh.allocFs hc1 hc2
  have hCoinsVmPlaced : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) :=
    fun hc1 hc2 => coinsFill_placed_ok_at_init_vmPreserved mmpl gh' W hh.allocFs hc1 hc2
  have hCoinsVm : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
    intro cStk hc1 hc2
    have hge : 80 ≤ cStk := by unfold cliCoinsFillStack extHookStack at hc1; omega
    exact signal_session_coins_fill_vm_placed_ok_of_mc_ms hge hc2
      (subroutine_ok_rocl_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
          (hookSat_withStack_keepsFs hh.memcpyRegionKeepsFs (cStk - 80))))
      (subroutine_ok_rocl_of_plain
        (ls_hook_ok_ultra_of_mem
          (prog := (blkPC_618).rebase (blkPl_618).base (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
          (hookSat_withStack_keepsFs hh.memsetRegionKeepsFs (cStk - 80))))
  apply subroutine_ok_of_sepWPp_init_placed
  rintro ⟨x, st0⟩ R s0 hpc hrun0 hpre hal
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced at hpre
  obtain ⟨hinv, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only at hpre1
  simp only [
    LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.slotFramePlaced,
    sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk, hFitsInit⟩,
    hcoinsLt, hm⟩ := hpre1
  have hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntryPlaced x s0 :=
    { pc := hpc
      run := hrun0
      inv := hinv
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  have hFitAll := hFits x st0 s0 hs0 hfilesOk hsInitOk hinitOk hcoinsLt hspk hFitsInit
  refine ⟨initEntryMemPlaced A lim st0 x stk s0, ?_, ?_⟩
  · simpa only [initEntryMemPlaced, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
            A lim InitEnv S stk).post (x, st0) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget.initSlotSpecPlaced
            A lim InitEnv S stk).onPanic (x, st0) s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    have hF1 := hFitAll.stage1
    refine initiate_stage1_placed_ok hh hStore hLoc
      hF1.fitTrustShim hF1.fitTrustPoll hF1.fitTrustClone hF1.envUntrusted
      hF1.fitSpkSer hF1.envBadSpk hF1.fitKpkSer hF1.envBadKpk
      hF1.fitLoadShim hF1.fitLoadPoll
      hS hinitOk hcoinsLt hstk hstk64 hspk hs0 hpostK hpanicK
      fun s2 be evsT1 evsT2 evsL1 evsL2 futT futL
          hevsT1 hfutTNZ hfutTAl hevsT2 hevsL1 hfutLNZ hfutLAl hevsL2 hs2 => ?_
    have hw1 : Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL :=
      ⟨hevsT1, hfutTNZ, hfutTAl, hevsT2, hevsL1, hfutLNZ, hfutLAl, hevsL2, hs2⟩
    have hF2 := hFitAll.stage2 hw1
    refine hStage2 hh @hCoinsVmPlaced hStore hLoc
      hF2.fitShim hF2.fitPoll hF2.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs2 hpostK hpanicK
      (fun evs1 evs2 box kp _ _ _ hkp hbox hevs1 hevs2 _ _ =>
        Entails.pure_left fun ⟨hnfit, _⟩ =>
          False.elim (hnfit (hF2.fitPqspkAlloc evs1 evs2 box kp hkp hbox hevs1 hevs2)))
      fun s3 kp ekASk ekAPk pqspkPtr opkId evs1 evs2 box hbox hevs1 hevs2 hs3 => ?_
    have hw2 : Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box :=
      ⟨hbox, hevs1, hevs2, hs3⟩
    have hF3 := hFitAll.stage3 hw1 hw2
    refine hStage3 hh @hCoinsVm @hCoinsRoCl hLoc hF3
      hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpostK hpanicK
      fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr evsS3 hevsS3 hs4 => ?_
    have hF4 := hFitAll.stage4 hw1 hw2 hevsS3 hs4
    refine initiate_stage4_placed_ok hh @hCoinsRoCl hLoc
      hF4.fitPreChain hF4.fitSpqr hF4.fitSess hF4.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpostK hpanicK
      fun s5 sg ss evsSpqr hevsSpqr hs5 => ?_
    have hF5 := hFitAll.stage5 hw1 hw2 hevsS3 hs4 hevsSpqr hs5
    exact initiate_stage5_placed_ok_with_panic hh hStore hLoc hF5
      hS hinitOk hcoinsLt hstk hstk64 hspk hs5 hpostK hpanicK

/-! ## 5. Top-Level `CliInitSlotOkPlacedAt` Producers -/

/-- Direct `SubsetA4InitCalleesPlaced` wrapper over `SpecPlacedBudget.cliInitiate_slotOk_placed`. -/
theorem cliInitSlotOkPlacedAt_of_a4 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) cliRunBudgets)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh' W)
    (hStage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
      Stage3PlacedOk A lim InitStateEnv InitEnv (Stage3Fit S) (Stage3Out S)
        mmpl gh' W X cliRunBudgets S)
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv
            (Stage3Fit S) (Stage3Out S) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W := by
  intro S sEnvs needs henv hfiles hS hinitOk hneed
  refine cliInitiate_slotOk_placed mmpl gh' W X cliRunBudgets S sEnvs needs
    hh hExist ha4 (hStage3 S hS) hS
    (fun F peer me _ hio => hinitOk ▸ hio)
    (hFits S hfiles hS hinitOk)
    (fun _ _ _ _ _ s0 sf _ _ _ _ _ hsteps _ hfail =>
      False.elim (lsProg_not_allocFailedIn_cliGhost mmpl gh' W hghNoAlloc s0 sf hsteps hfail))
    henv hneed

/-- Generic `eEnvs` / `InitLocalCalleesPlaced` producer for `CliInitSlotOkPlacedAt` at
`cliGhostExterns gh' (cliExternsPlaced mmpl W)`. -/
theorem cliInitSlotOkPlacedAt_of_local [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget.RunHooksPlaced
      W A lim (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs
      (cliGhostExterns gh' (cliExternsPlaced mmpl W)) cliRunBudgets)
    (hLocal : ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
      InitLocalCalleesPlaced A lim InitStateEnv mmpl gh' W stk)
    (hStage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
      Stage3PlacedOk A lim InitStateEnv InitEnv (Stage3Fit S) (Stage3Out S)
        mmpl gh' W X cliRunBudgets S)
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv
            (Stage3Fit S) (Stage3Out S) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W := by
  intro S sEnvs needs henv hfiles hS hinitOk hneed stk h1 h2
  dsimp only [slotsOfPlaced, mkSlot] at h1 ⊢
  have hstk : cliInitiateNeed cliRunBudgets ≤ stk := hneed ▸ h1
  rw [henv]
  have h521 := cliInitiate_placed_ok_of_local mmpl gh' W X cliRunBudgets S
    hh hExist hLocal (hStage3 S hS) hS
    (fun _ _ _ _ hio => hinitOk ▸ hio)
    stk hstk h2 (hFits S hfiles hS hinitOk hstk h2)
  have h579 := transfer_withLsCodeRoLoaded
    (callerProg := lsProg_579 (cliGhostExterns gh' (cliExternsPlaced mmpl W)))
    (hi := (by decide : 579 < 619)) h521
  exact subroutine_ok_semInitSlot_of_noAllocFail h579
    (lsProg_not_allocFailedIn_cliGhost mmpl gh' W hghNoAlloc)

/-- Proves `CliInitSlotOkPlacedAt` at `cliGhostExterns gh' (cliExternsPlaced mmpl W)` from
`W3GhostHooks`, `spqrInitialState` (Block 327), `verifySignature` (Block 203), `Stage3PlacedOk`,
`ExternNoAllocFailed`, and `CliInitiateBudgetFits`. -/
theorem cliInitSlotOkPlacedAt_of_ghost [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hHooks : W3GhostHooks mmpl gh' W A lim ReadEnv)
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hStage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
      Stage3PlacedOk A lim InitStateEnv InitEnv (Stage3Fit S) (Stage3Out S)
        mmpl gh' W X cliRunBudgets S)
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3Fit S) (Stage3Out S) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W :=
  let hh := initRunHooks_of_w3GhostHooks hHooks
  cliInitSlotOkPlacedAt_of_local mmpl gh' W X
    hh
    (w3Exist_placed_ok_of_ghost mmpl gh' W A lim ReadEnv hHooks)
    (fun hstk hstk64 =>
      w3Local_placed_ok_of_seams mmpl gh' W A lim InitStateEnv cliRunBudgets
        hh hSpqrInit hVerifySig hstk hstk64)
    hStage3 hghNoAlloc hFits

theorem cliInitSlotOkPlacedAt_of_ghost_eq [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : ∀ _S : RunSem, InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hH : H = cliGhostExterns gh' (cliExternsPlaced mmpl W))
    (hHooks : W3GhostHooks mmpl gh' W A lim ReadEnv)
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hStage3 : ∀ (S : RunSem), S.initiate = initDef X ⟨W.C, W.Q⟩ →
      Stage3PlacedOk A lim InitStateEnv InitEnv (Stage3Fit S) (Stage3Out S)
        mmpl gh' W X cliRunBudgets S)
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3Fit S) (Stage3Out S) W X x s0 st0) :
    CliInitSlotOkPlacedAt H A lim InitEnv X W :=
  hH ▸ cliInitSlotOkPlacedAt_of_ghost mmpl gh' W X
    hHooks hSpqrInit hVerifySig hStage3 hghNoAlloc hFits

/-- Ready-to-use `stage3OkEvents` specialization of `cliInitSlotOkPlacedAt_of_ghost` with Stage 3
pre-discharged via `stage3PlacedOk_okEvents`. -/
theorem cliInitSlotOkPlacedAt_of_okEvents [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hHooks : W3GhostHooks mmpl gh' W A lim ReadEnv)
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W :=
  cliInitSlotOkPlacedAt_of_ghost mmpl gh' W X
    hHooks hSpqrInit hVerifySig
    (fun S _ => stage3PlacedOk_okEvents A lim InitStateEnv InitEnv mmpl gh' W X cliRunBudgets S)
    hghNoAlloc hFits

theorem cliInitSlotOkPlacedAt_of_okEvents_eq [LibsignalPlacement] {M : AllocCostModel}
    {H : LibsignalHooks}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hH : H = cliGhostExterns gh' (cliExternsPlaced mmpl W))
    (hHooks : W3GhostHooks mmpl gh' W A lim ReadEnv)
    (hSpqrInit : subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A lim InitStateEnv W.C.F)))
    (hVerifySig : ∀ (Y : UnreachedPqxdhPrimitives),
      subroutine_ok (initProgPlaced mmpl gh' W) (lsmpl.base 203)
        (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))))
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs ReadEnv) InitStateEnv InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    CliInitSlotOkPlacedAt H A lim InitEnv X W :=
  hH ▸ cliInitSlotOkPlacedAt_of_okEvents mmpl gh' W X
    hHooks hSpqrInit hVerifySig hghNoAlloc hFits

/-- Convenience `SpqrV1PlacedSeamsBudget` specialization of `cliInitSlotOkPlacedAt_of_okEvents`. -/
theorem cliInitSlotOkPlacedAt_of_spqrSeams [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {envs : CliSlotEnvs}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh' : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives)
    (hHooks : W3GhostHooks mmpl gh' W A lim envs.readFile)
    (hSpqr : SpqrV1PlacedSeamsBudget mmpl gh' W A lim envs)
    (hghNoAlloc : ExternNoAllocFailed (cliGhostExterns gh' (fun _ => none)))
    (hFits : ∀ (S : RunSem),
      S.filesOk = filesOk₀ scopeIn (fun _ => True) →
      S.initiate = initDef X ⟨W.C, W.Q⟩ →
      S.initOk = InitOk₀ ⟨W.C, W.Q⟩ →
      ∀ {stk : Nat}, cliInitiateNeed cliRunBudgets ≤ stk → stk ≤ 2 ^ 63 →
        ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
          AtInitEntryPlaced x s0 →
          S.filesOk x.F x.peer.val x.me.val →
          S.initOk x.F x.peer.val x.me.val →
          InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
          x.coins.length < 2 ^ 63 →
          stk ≤ s0.sp.toNat →
          FitsEnv M lim st0 (InitEnv x) →
          CliInitiateBudgetFits M lim (cliExistingStoreCalleesEnvs envs.readFile)
            envs.spqrInitState InitEnv
            (Stage3OkEventsFit lim InitEnv W X) (Stage3OkEventsOut W X) W X x s0 st0) :
    CliInitSlotOkPlacedAt (cliGhostExterns gh' (cliExternsPlaced mmpl W))
      A lim InitEnv X W :=
  cliInitSlotOkPlacedAt_of_okEvents mmpl gh' W X
    hHooks hSpqr.spqrInitialState_initProg hSpqr.verifySignature hghNoAlloc hFits

end

end LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
