/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.KyberKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.PreKeyKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.SelfKitOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedPrePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureSpeOwned
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Base Callees and Bounds

Generalizes placed Stage P2 `FsAt` lifts, `ResponderPqxdhPlacedHookContracts`, and Stage P2 callee
projections (`drop_spe2`, `drop_session_structure`, `<PublicKey>::serialize`,
`<PrivateKey>::calculate_agreement`, `hkdfExtract`, and `hkdfExpandMultiInfo`) to
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoGames.LibsignalSessionApi (ApiError)
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement
  lsBlackBoxU8Sym lsRustDeallocSym lsRustNoAllocShimSym lsmpl
  ls_subroutine_ok_of_block
  subroutine_ok_withLsCodeLoaded_of_plain withLsCl withLsCodeLoaded
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (
  stageP2EnvOk stageP2Quiet stageP2V1CallStack
)
open CryptoVerification.E2E (
  UnreachedPqxdhPrimitives kemDecapsHook modelPrims toEdwardsHook torsionFreeHook
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  DalekMontToEdGhost Primitives StructuralPrims cryptoBoolRegStubSpec
)
open CryptoVerification.E2E.Pqxdh.ResponderCore (
  PrimitivesMatchCrypto lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym
  ofSignalPqxdhPrimitives
)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsAt FsFiles KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec TraceFsSound speErrAt
)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf (IdentitySelfStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (
  HkdfPlacedHooks diffieHellmanSpec lsMemsetSym withLsCodeRoLoaded zeroizeSecretSpec
)
open CryptoVerification.LibsignalTripleRatchet.Getters (withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys (
  lsDhSym lsRustAllocSym lsSharedDropSym lsStaticDropSym
)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced cliHookTablePlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (decResAt)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_memcpy_some
  cliGhostExterns_memset_some cliGhostExterns_other cliGhostExterns_shim
)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (
  DpKitStk cliKitStk cliModelPrims_matchCrypto cliPollIdKitPlaced cliPollKpkKitPlaced
  cliPollKpkPlaced_quiet cliPollPkKitPlaced cliPollPkPlaced_quiet cliPollSelfKitPlaced
  cliPollSelfPlaced_quiet cliPollSpkKitPlaced cliPollSpkPlaced_quiet dpClosSubStack
  dpPollProgPlaced
)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (
  blackBox_row_placed cliExternsPlaced_compress256 cliExternsPlaced_kemDecaps_sat
  cliExternsPlaced_toEdwards_sat cliExternsPlaced_torsionFree_sat
  cliGhostExterns_sat_of_cliExternsPlaced kemDecaps_row_placed
  toEdwards_row_placed torsionFree_row_placed
)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (hookSat_withVmPreserved withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget (
  drop_session_structure4_placed_cl_ok_at drop_session_structure4_placed_ok_at
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget (
  PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
  handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Reloc.DropSpe2PlacedBudget (
  drop_spe2_placed_ok_at
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget (
  PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk
  pqxdhCalculateAgreement_placed_frozen_ok_of_block pqxdhCalculateAgreement_placed_ok_of_block
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget (
  PqxdhPlacedHookContracts createChain_placed_ok_of_block createChain_placed_ok_x_of_block
  cryptoBoolRegStubBudgetSpec dalekMontToEdStubBudgetSpec
  handshakeKeysDerive_placed_ok_of_block handshakeKeysDerive_placed_vm_ok_of_block
  kyberDecapsStubBudgetSpec pqxdhHkdfExpandMultiInfo_placed_ok pqxdhHkdfExtract_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget (
  CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
  cliExternsPlaced_diffieHellman_budget_sat
  cliExternsPlaced_sharedSecretDrop_budget_sat cliExternsPlaced_staticSecretDrop_budget_sat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec noAllocShim_hookOk publicKeySerializeSpec publicKeySerializeSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget (
  public_key_serialize_placed_ok public_key_serialize_placed_ok_x
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (createChainSpec createChainSpecX)

/-! ## 1. Placed Call-Stack Bound & `FsAt` Lift -/

/-- Placed `stageP2V1CallStack` fits within `dpClosSubStack B` for the CLI Poll store kits. -/
theorem stageP2V1CallStack_le_subStack_placed {A : RustAlloc} [LibsignalPlacement]
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    stageP2V1CallStack
      (cliPollSpkKitPlaced A F0 spkId (cliKitStk B))
      (cliPollKpkKitPlaced A F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKitPlaced A F0 opkIdWord (cliKitStk B))
      (cliPollSelfKitPlaced A F0 peer (cliKitStk B)) ≤ dpClosSubStack B :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.stageP2V1CallStack_le_subStack_placed
    F0 peer spkId kpkId opkIdWord kbk B

/-- Generic `TraceFsSound` lift from `FsAt (fun f => f = F0) True` to placed
`FsAt (stageP2EnvOk...) (stageP2Quiet...)` at any representation allocator `A_r : RustAlloc`. -/
theorem cliPollStageP2_fsAt_of_hook_placed {A_r : RustAlloc}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks} [LibsignalPlacement]
    (hfsHook : TraceFsSound (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A_r F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A_r F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A_r F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A_r F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A_r F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A_r F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A_r F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s := by
  rcases hfs with hall | ⟨_, _, hf⟩
  · exact .inl fun f => ⟨hall f, hall f, hall f, hall f⟩
  · exact .inr
      ⟨⟨cliPollSpkPlaced_quiet F0 spkId (cliKitStk B),
        cliPollKpkPlaced_quiet F0 kpkId spkId kbk (cliKitStk B),
        cliPollPkPlaced_quiet F0 opkIdWord (cliKitStk B),
        cliPollSelfPlaced_quiet F0 peer (cliKitStk B)⟩,
       hfsHook, ⟨hf, hf, hf, hf⟩⟩

/-- Lift `FsAt (fun f => f = F0) True` + `hh.fs` (`SkeletonPlacedBudget.RunHooksPlaced`) to placed
`FsAt (stageP2EnvOk...) (stageP2Quiet...)` at `A.repAlloc`. -/
theorem cliPollStageP2_fsAt_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  cliPollStageP2_fsAt_of_hook_placed
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518)
    F0 peer spkId kpkId opkIdWord kbk B hfs

/-- Variant of `cliPollStageP2_fsAt_placed` accepting `ClosureStagesStmtPlacedBudget.RunHooksPlaced`. -/
theorem cliPollStageP2_fsAt_stages_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {g : CliGhostHooks} {W : CliHooks}
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStagesStmtPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey)
    (B : RunBudgets) {s : State}
    (hfs : FsAt (fun f => f = F0) True
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s) :
    FsAt
      (stageP2EnvOk
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollIdKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (stageP2Quiet
        (cliPollSpkKitPlaced A.repAlloc F0 spkId (cliKitStk B))
        (cliPollKpkKitPlaced A.repAlloc F0 kpkId spkId kbk (cliKitStk B))
        (cliPollPkKitPlaced A.repAlloc F0 opkIdWord (cliKitStk B))
        (cliPollSelfKitPlaced A.repAlloc F0 peer (cliKitStk B)))
      (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) s :=
  cliPollStageP2_fsAt_of_hook_placed
    (hh.fs (dpPollProgPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))) 518)
    F0 peer spkId kpkId opkIdWord kbk B hfs

/-! ## 2. Placed Error-Payload Entailments (`b := 0#64`) -/

/-- Placed `get_signed_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollSpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (spkId : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSpkKitPlaced A F0 spkId σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSpkKitPlaced A F0 spkId σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSpk_getErr_entails_decResAt_anyHeap_placed
    A F0 spkId σ outPtr e err

/-- Placed `get_kyber_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollKpk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (kpkId spkId : BitVec 32) (kbk : PublicKey) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollKpkKitPlaced A F0 kpkId spkId kbk σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollKpk_getErr_entails_decResAt_anyHeap_placed
    A F0 kpkId spkId kbk σ outPtr e err

/-- Placed `get_pre_key` error payload entails `decResAt A outPtr (.error err) ∗ anyHeap`. -/
theorem cliPollPk_getErr_entails_decResAt_anyHeap_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (opkIdWord : BitVec 32) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollPkKitPlaced A F0 opkIdWord σ).GetErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollPkKitPlaced A F0 opkIdWord σ).getErr outPtr e ⊢
      decResAt A outPtr (.error err) ∗ anyHeap :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollPk_getErr_entails_decResAt_anyHeap_placed
    A F0 opkIdWord σ outPtr e err

/-- Placed `get_identity_key_pair` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_kpErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).KpErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).kpErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_kpErr_entails_decResAt_err_placed
    A F0 peer σ outPtr e err

/-- Placed `get_local_registration_id` error payload entails `decResAt A outPtr (.error err)`. -/
theorem cliPollSelf_regIdErr_entails_decResAt_err_placed [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk)
    (outPtr : BitVec 64)
    (e : (cliPollSelfKitPlaced A F0 peer σ).RegIdErr)
    (err : ApiError AddrVal Unit) :
    speErrAt (cliPollSelfKitPlaced A F0 peer σ).regIdErr outPtr e ⊢
      decResAt A outPtr (.error err) :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_regIdErr_entails_decResAt_err_placed
    A F0 peer σ outPtr e err

/-! ## 3. Budget-Threaded `PqxdhPlacedHookContracts` at `cliGhostExterns` -/

/-- `HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W))` from
`g.memset = some memsetHook`, `g.memcpy = some memcpyHook`, and `cliHookTablePlaced mmpl W`. -/
theorem instHkdfPlacedHooks_cli_poll (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks)
    (hMs : g.memset = some memsetHook)
    (hMc : g.memcpy = some memcpyHook) :
    HkdfPlacedHooks W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) where
  memset := cliGhostExterns_memset_some g (cliExternsPlaced mmpl W) hMs
  memcpy := cliGhostExterns_memcpy_some g (cliExternsPlaced mmpl W) hMc
  compress256 := (cliGhostExterns_other g (cliExternsPlaced mmpl W)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (cliExternsPlaced_compress256 mmpl W)

private theorem setMem_vm (s : State) {m : Memory} (hp : ∀ a : BitVec 64, m.perm a = s.mem.perm a) :
    VmPreserved s (s.setMem m) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, hp, fun _ _ _ => rfl⟩

private theorem writeBytes_perm_eq (m : Memory) (p : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes p bs).perm a = m.perm a :=
  congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm m p bs) a

private theorem hookSat_cli_vm {α : Type} (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {sym : String} {f : State → State} {spec : Spec α}
    (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (hsat : HookSat (cliExternsPlaced mmpl W) sym spec)
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookSat (cliExternsPlaced mmpl W) sym (withVmPreserved spec) := by
  refine hookSat_withVmPreserved hsat fun g hg s => ?_
  have hfeq : cliExternsPlaced mmpl W sym = some f := cliExternsPlaced_row mmpl W hrow
  rw [hfeq] at hg
  injection hg with hfg
  subst hfg
  exact hvm s

private theorem hookSat_noAllocShimBudget_of_withVmPreserved {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec)) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec,
      noAllocShimBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem kemDecapsHook_vm (W : CliHooks) (s : State) :
    VmPreserved s (kemDecapsHook W.Q.decaps s) := by
  unfold kemDecapsHook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  exact setMem_vm s (writeBytes_perm_eq _ _ _)

private theorem toEdwardsHook_vm (W : CliHooks) (s : State) :
    VmPreserved s (toEdwardsHook W.Q.montToEd s) := by
  unfold toEdwardsHook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  dsimp only
  cases W.Q.montToEd (CryptoVerification.E2E.readVecN s.mem (s.readReg64 .x0) 32)
      ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
  | none =>
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun a =>
      congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write64_norm _ _ _) a, fun _ _ _ => rfl⟩
  | some p =>
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun a =>
      (writeBytes_perm_eq _ _ _ a).trans
        (congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write64_norm _ _ _) a), fun _ _ _ => rfl⟩

private theorem torsionFreeHook_vm (W : CliHooks) (s : State) :
    VmPreserved s (torsionFreeHook W.Q.isTorsionFree s) := by
  unfold torsionFreeHook CryptoVerification.LibsignalAesCbc.returnToLinkRegister
  exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- `noAllocShimBudgetSpec` `HookSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem cliExternsPlaced_noAllocShimBudget_sat (mmpl : Obj.MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) (hShim : g.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec :=
  ⟨hookNoop, (cliGhostExterns_shim g (cliExternsPlaced mmpl W)).trans (congrArg some hShim),
    noAllocShim_hookOk⟩

/-- `VmPreserved`-strengthened `HookSat` for `kyber::decapsulate` at `cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_kemDecaps_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) :
    HookSat (cliExternsPlaced mmpl W) lsKyberDecapsSym
      (kyberDecapsStubBudgetSpec (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) :=
  hookSat_cli_vm mmpl W (kemDecaps_row_placed mmpl W) (cliExternsPlaced_kemDecaps_sat mmpl W X)
    (kemDecapsHook_vm W)

/-- Honest `VmPreserved`-strengthened responder contract for `MontgomeryPoint::to_edwards`:
matches `ResponderCore.dalekMontToEdStubSpec` (`dalekMontToEdOutAt`), which on `montToEd = none`
leaves `[outPtr + 8.. outPtr + 168)` as `memRegion (outPtr + 8#64) 160` (matching the trusted
`toEdwardsHook`, unlike `CryptoCalleesPlacedBudget.dalekMontToEdStubBudgetSpec`, which opened
`Initiator.dalekMontToEdStubSpec` and required 160 zero bytes on `none`). -/
def dalekMontToEdResponderBudgetSpec (P : Primitives) : Spec DalekMontToEdGhost :=
  withVmPreserved (CryptoVerification.E2E.Pqxdh.ResponderCore.dalekMontToEdStubSpec P)

/-- `VmPreserved`-strengthened `HookSat` for `MontgomeryPoint::to_edwards` at
`cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_toEdwards_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) :
    HookSat (cliExternsPlaced mmpl W) lsDalekMontToEdSym
      (dalekMontToEdResponderBudgetSpec (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) := by
  have hbase : HookSat (cliExternsPlaced mmpl W) lsDalekMontToEdSym
      (CryptoVerification.E2E.Pqxdh.ResponderCore.dalekMontToEdStubSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))) := by
    rcases cliExternsPlaced_toEdwards_sat mmpl W X (img := default) with ⟨f, hrow, hok⟩
    exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
      hok ⟨g.inBytes, g.signBit, g.inPtr, g.outPtr⟩ R s0 hrun hpre hsp⟩
  exact hookSat_cli_vm mmpl W (toEdwards_row_placed mmpl W) hbase (toEdwardsHook_vm W)

/-- `VmPreserved`-strengthened `HookSat` for `EdwardsPoint::is_torsion_free` at
`cliExternsPlaced mmpl W`. -/
theorem cliExternsPlaced_torsionFree_budget_sat (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) :
    HookSat (cliExternsPlaced mmpl W) lsDalekTorsionFreeSym
      (cryptoBoolRegStubBudgetSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)).isTorsionFree 160) := by
  have hbase : HookSat (cliExternsPlaced mmpl W) lsDalekTorsionFreeSym
      (cryptoBoolRegStubSpec
        (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)).isTorsionFree 160) := by
    rcases cliExternsPlaced_torsionFree_sat mmpl W X (img := default) with ⟨f, hrow, hok⟩
    exact ⟨f, hrow, fun g R s0 hrun hpre hsp =>
      hok ⟨g.inPtr, g.inBytes⟩ R s0 hrun hpre hsp⟩
  exact hookSat_cli_vm mmpl W (torsionFree_row_placed mmpl W) hbase (torsionFreeHook_vm W)

/-- Combined budget-threaded external-hook contract bundle for `ResponderCore` using the honest
`ResponderCore.dalekMontToEdStubSpec` (`dalekMontToEdOutAt`) contract satisfied unconditionally by
`cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
structure ResponderPqxdhPlacedHookContracts [LibsignalPlacement] (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooks C.F H
  dh               : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdResponderBudgetSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)

/-- Bridge to `CryptoCalleesPlacedBudget.PqxdhPlacedHookContracts` when the caller supplies the
stronger zero-padded `Initiator.dalekMontToEdStubSpec` contract. -/
theorem ResponderPqxdhPlacedHookContracts.toCryptoCallees [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hmont : HookSat H lsDalekMontToEdSym (dalekMontToEdStubBudgetSpec P)) :
    PqxdhPlacedHookContracts M P C A lim H where
  hkdf := hH.hkdf
  dh := hH.dh
  sharedDrop := hH.sharedDrop
  staticDrop := hH.staticDrop
  blackBox := hH.blackBox
  noAllocShim := hH.noAllocShim
  alloc := hH.alloc
  dealloc := hH.dealloc
  kyberDecaps := hH.kyberDecaps
  dalekMontToEd := hmont
  dalekTorsionFree := hH.dalekTorsionFree

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok hP hi

/-- `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok hP hi

/-- `<HandshakeKeys>::derive` (`VmPreserved`, Block `59`) on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_vm_ok_of_block hWF hP hi

/-- `<HandshakeKeys>::derive` (`RustCliAllocBudget`, Block `59`) on any caller
block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_ok_of_block hWF hP hi

/-- `<RootKey>::create_chain` (Block `40`) on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- `<RootKey>::create_chain` at `createChainStackX` (Block `40`) on any caller
block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContracts.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_x_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

/-- `HkdfPlacedHooksExactSat`-widened external-hook contract bundle for `ResponderCore`, replacing
`HkdfPlacedHooks C.F H` with `HkdfPlacedHooksExactSat C.F H` plus
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec` (`CliGhostAllocHooks`-derivable under A2''). -/
structure ResponderPqxdhPlacedHookContractsExactSat [LibsignalPlacement]
    (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksExactSat C.F H
  memsetBudget     : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec
  dh               : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdResponderBudgetSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)

/-- Bundle projection: `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on any caller block `i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ := hH.hkdf
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    hH.memsetBudget (F := C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExtract_placed_ok_sat
    hP hi

/-- Bundle projection: `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on any caller block
`i < 619`. -/
theorem ResponderPqxdhPlacedHookContractsExactSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : ResponderPqxdhPlacedHookContractsExactSat M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ := hH.hkdf
  have _ := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat.of_exactSat
    hH.memsetBudget (F := C.F)
  exact LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat.pqxdhHkdfExpandMultiInfo_placed_ok_sat
    hP hi

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g` and `HookSat` contracts for `alloc`, `dealloc`, and `noAllocShim`. -/
theorem cliResponderPqxdhHookContractsPlaced_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) := by
  have hExactB :
      LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat.HkdfPlacedHooksExactBudgetSat
        W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
    { memset :=
        LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget.cliExternsPlaced_sessionMemsetRegion_budget_sat
          mmpl g W hG
      memcpy := by
        obtain ⟨f, hf, _⟩ := hG.memcpy
        exact ⟨f,
          LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer.cliGhostExterns_memcpy_some
            g (cliExternsPlaced mmpl W) hf,
          hG.memcpy_exact f hf⟩
      compress256 := (cliGhostExterns_other g (cliExternsPlaced mmpl W)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_compress256 mmpl W) }
  refine
    { hkdf := hExactB.toExactSat
      memsetBudget := hExactB.memset
      dh := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_diffieHellman_budget_sat mmpl W)
      sharedDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W)
      staticDrop := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W)
      blackBox := (cliGhostExterns_other g (cliExternsPlaced mmpl W)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W))
      noAllocShim := hnoAllocShim
      alloc := halloc
      dealloc := hdealloc
      kyberDecaps := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_kemDecaps_budget_sat mmpl W X)
      dalekMontToEd := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_toEdwards_budget_sat mmpl W X)
      dalekTorsionFree := cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_torsionFree_budget_sat mmpl W X) }

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`. -/
theorem cliResponderPqxdhHookContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat X mmpl g W hG
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq)

/-- `ResponderPqxdhPlacedHookContractsExactSat` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g` and
`SkeletonPlacedBudget.RunHooksPlaced A lim (cliGhostExterns g (cliExternsPlaced mmpl W))`. -/
theorem cliResponderPqxdhHookContractsPlaced_of_runHooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hh : LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget.RunHooksPlaced
      A lim (cliGhostExterns g (cliExternsPlaced mmpl W))) :
    ResponderPqxdhPlacedHookContractsExactSat M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      W.C A lim (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  cliResponderPqxdhHookContractsPlaced_of_hookSat X mmpl g W hG
    hh.codecHooks.alloc hh.codecHooks.dealloc
    (hookSat_noAllocShimBudget_of_withVmPreserved hh.codecHooks.shim)

/-! ## 4. Placed Budget Stage P2 Callee Projections at `cliGhostExterns` -/

/-- `drop_spe2` (`dropSpeSpec M A lim`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `hdealloc`. -/
theorem cliDropSpe2_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :=
  drop_spe2_placed_ok_at hdealloc hi

/-- `drop_spe2` (`dropSpeSpec M A lim`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliDropSpe2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 511)
      (withLsCodeLoaded lsmpl (withLsRoLoaded lsmpl (dropSpeSpec M A lim))) :=
  cliDropSpe2_placed_ok_of_dealloc mmpl g W (cliExternsPlaced_dealloc_budget_sat mmpl g W hG) hi

/-- `drop_session_structure` (`dropSessionStructureLocal2Spec M A lim`) on any caller block
`i < 619` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `hdealloc`. -/
theorem cliDropSessionStructure_placed_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_ok_at hdealloc hi

/-- `withLsCl` variant of `cliDropSessionStructure_placed_ok_of_dealloc`. -/
theorem cliDropSessionStructure_placed_cl_ok_of_dealloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCl lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  drop_session_structure4_placed_cl_ok_at hdealloc hi

/-- `drop_session_structure` (`dropSessionStructureLocal2Spec M A lim`) on any caller block
`i < 619` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliDropSessionStructure_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) :=
  cliDropSessionStructure_placed_ok_of_dealloc mmpl g W
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG) hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc`. -/
theorem cliPublicKeySerialize_placed_ok_at_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok
        hnoAllocShim
        halloc))
    hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpecX M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc`. -/
theorem cliPublicKeySerialize_placed_ok_x_at_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 205)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (public_key_serialize_placed_ok_x
        hnoAllocShim
        halloc))
    hi

/-- `<PublicKey>::serialize` (`publicKeySerializeSpec M A lim`) on any caller block `i < 619`
at `cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliPublicKeySerialize_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hG : CliGhostAllocHooks M A lim g)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)) :=
  cliPublicKeySerialize_placed_ok_at_of_alloc mmpl g W
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_noAllocShimBudget_sat mmpl g W hG.shim_eq) hi

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc` and `hdealloc`. -/
theorem cliPqxdhCalculateAgreement_placed_ok_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  let _ := hdealloc
  pqxdhCalculateAgreement_placed_ok_of_block
    (cliModelPrims_matchCrypto X W)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_diffieHellman_budget_sat mmpl W))
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W))
    ((cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
    hnoAllocShim
    halloc
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W))
    hi

/-- `PqxdhCalculateAgreementPlacedFrozenOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `halloc` and `hdealloc`. -/
theorem cliPqxdhCalculateAgreement_frozen_placed_ok_of_hookSat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (halloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustAllocSym
      (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustDeallocSym
      (rustCliDeallocBudgetSpec M A lim))
    (hnoAllocShim : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsRustNoAllocShimSym
      noAllocShimBudgetSpec := by exact cliExternsPlaced_noAllocShimBudget_sat mmpl g W)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  let _ := hdealloc
  pqxdhCalculateAgreement_placed_frozen_ok_of_block
    (cliModelPrims_matchCrypto X W)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_diffieHellman_budget_sat mmpl W))
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_sharedSecretDrop_budget_sat mmpl W))
    ((cliGhostExterns_other g (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (cliExternsPlaced_row mmpl W (blackBox_row_placed mmpl W)))
    hnoAllocShim
    halloc
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_staticSecretDrop_budget_sat mmpl W))
    hi

/-- `PqxdhCalculateAgreementPlacedOk` on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliPqxdhCalculateAgreement_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩))
      A lim callerProg :=
  (cliResponderPqxdhHookContractsPlaced X mmpl g W hG).calculateAgreement_ok
    (cliModelPrims_matchCrypto X W) hi

/-- `PqxdhHkdfExtractPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliPqxdhHkdfExtract_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  exact (cliResponderPqxdhHookContractsPlaced X mmpl g W hG).hkdfExtract_ok
    (cliModelPrims_matchCrypto X W) hi

/-- `PqxdhHkdfExpandMultiInfoPlacedOk` (`HandshakeDeriveBudget`) on any caller block `i < 619` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` from `CliGhostAllocHooks M A lim g`. -/
theorem cliPqxdhHkdfExpandMultiInfo_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (X : UnreachedPqxdhPrimitives) (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    {callerProg : Program} {i : Nat}
    [IsLsBlockProg callerProg i (cliGhostExterns g (cliExternsPlaced mmpl W))]
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk
      (ofSignalPqxdhPrimitives (modelPrims X ⟨W.C, W.Q⟩)) callerProg := by
  exact (cliResponderPqxdhHookContractsPlaced X mmpl g W hG).hkdfExpandMultiInfo_ok
    (cliModelPrims_matchCrypto X W) hi

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1BasePlacedBudget
