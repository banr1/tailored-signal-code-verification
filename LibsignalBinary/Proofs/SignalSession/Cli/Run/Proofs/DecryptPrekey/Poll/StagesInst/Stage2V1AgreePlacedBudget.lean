/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1FoldsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFoldPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` CLI Poll Stage P2 V1 Agreement Helpers

Generalizes `kyberPtr ≠ 0` duplication bridges, `cliPoll*KitPlaced` pre-key canonicality lemmas,
and `pathA_acceptInput_agree_placed` to `RustCliAllocBudget M` and `{A : RustAlloc}`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet

open CryptoGames.LibsignalSession (PublicKey SignalMessage)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits (OpkOkWitness hdrOpkIdBv? mkP2AcceptKeysInput opkOkEvs opkOkKeyBytes opkOkRel opkOkUpdate)
open CryptoVerification.E2E (PEParams PreKeyMessageFields ResponderPreKeySecrets acceptInput keyPairOf)
open CryptoVerification.E2E.Pqxdh.Initiator (bytesToBv8 ofSignalPqxdhAcceptKeysInput)
open CryptoVerification.E2E.Pqxdh.ResponderCore (bytesToBv8_vecU8 vecU8_length)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles KyberPreKeyStoreSpec PreKeyStoreSpec SignedPreKeyStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPair KyberPreKeyRecord PreKeyRecord SignedPreKeyRecord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunProofs (DecPkOk₀ PreKeyFilesWf pkStoreKeys)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection ProofLib.Variant
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (DpKitStk PathAEntryWords cliKitStk cliPollIdKitPlaced cliPollKpkKitPlaced
   cliPollKpk_wf_of_preKeysWf_ext cliPollPkKitPlaced cliPollPk_wf_of_preKeysWf_ext
   cliPollSelfKitPlaced cliPollSpkKitPlaced cliPollSpk_wf_of_preKeysWf_ext
   dpClosSubStack mkPathAHdr pathA_acceptInput_agree_ext)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlotPlacedBudget
  (DpPollGhostStateBudget dpSlotPollKStatePlaced)

/-! ## Program-Polymorphic & Pure Path A Agreement Re-Exports -/

abbrev sepWPp_with_steps :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.sepWPp_with_steps

abbrev sepWPp_drop_steps :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.sepWPp_drop_steps

abbrev idKeyPair_keyPairOf_privateKey :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.idKeyPair_keyPairOf_privateKey

abbrev decPkDef_pathA_accept_none_anyReg :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.decPkDef_pathA_accept_none_anyReg

abbrev p2BobInitSessionV1_eq_pathAInitState_ext :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2BobInitSessionV1_eq_pathAInitState_ext

abbrev p2BobInitSessionV1_eq_pathAInitState :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.p2BobInitSessionV1_eq_pathAInitState

abbrev sessionExtraRel_pathAInitSession_ext :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.sessionExtraRel_pathAInitSession_ext

abbrev sessionExtraRel_pathAInitSession :=
  @CryptoVerification.SignalSession.Cli.RunProofs.Poll.sessionExtraRel_pathAInitSession

/-! ## 1. Budget-Threaded `kyberPtr ≠ 0` Duplication Bridges -/

abbrev stageP2PreAtPlaced :=
  @Stage2V1FoldsPlacedBudget.stageP2PreAtPlaced

abbrev pathAInnerFramePlaced :=
  @Stage2V1FoldsPlacedBudget.pathAInnerFramePlaced

abbrev pathAInnerFramePlacedExt :=
  @Stage2V1FoldsPlacedBudget.pathAInnerFramePlacedExt

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFramePlaced A_r`. -/
theorem pathAInnerFrame_dup_kyberPtr_placed_alloc {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced A_r y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFramePlaced A_r y m i rngPtr sp :=
  Stage2V1FoldsPlacedBudget.pathAInnerFrame_dup_kyberPtr_placed A_r y m i rngPtr sp

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFramePlaced A.repAlloc`. -/
theorem pathAInnerFrame_dup_kyberPtr_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced A.repAlloc y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFramePlaced A.repAlloc y m i rngPtr sp :=
  Stage2V1FoldsPlacedBudget.pathAInnerFrame_dup_kyberPtr_placed A.repAlloc y m i rngPtr sp

/-- Duplicate `⌜y.g.msgG.kyberPtr ≠ 0#64⌝` out of `pathAInnerFramePlaced (A.atState lim st_b s1)`. -/
theorem pathAInnerFrame_dup_kyberPtr_placed_atState {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (rngPtr sp : BitVec 64) :
    pathAInnerFramePlaced (A.atState lim st_b s1) y m i rngPtr sp ⊢
      ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗ pathAInnerFramePlaced (A.atState lim st_b s1) y m i rngPtr sp :=
  Stage2V1FoldsPlacedBudget.pathAInnerFrame_dup_kyberPtr_placed
    (A.atState lim st_b s1) y m i rngPtr sp

/-- Kit- and allocator-polymorphic `stageP2PreAt_dup_kyberPtr_placed` over arbitrary
`{A_s A_r : RustAlloc}` and store kits `{spkKit kpkKit pkKit ikit}`. -/
theorem stageP2PreAt_dup_kyberPtr_placed_kits {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    {A_s A_r : RustAlloc}
    {spkKit : SignedPreKeyStoreSpec A_s 0#64}
    {kpkKit : KyberPreKeyStoreSpec A_s 0#64}
    {pkKit : PreKeyStoreSpec A_s 0#64}
    {ikit : IdentityStoreSpec A_s 0#64}
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (stPk : pkKit.PkState) (stId : ikit.IdState) :
    stageP2PreAtPlaced A_s spkKit kpkKit pkKit ikit
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced A_s spkKit kpkKit pkKit ikit
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      stSpk stKpk stPk stId
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) :=
  Stage2V1FoldsPlacedBudget.stageP2PreAt_dup_kyberPtr_placed
    y m i w s0 sp fp rngPtr v_a8 v_b8 v_d0 stSpk stKpk stPk stId

/-- `RustAlloc`-polymorphic `stageP2PreAt_dup_kyberPtr_placed` specialized to `cliPoll*KitPlaced A_s`
and `pathAInnerFramePlaced A_r`. -/
theorem stageP2PreAt_dup_kyberPtr_placed_ext {M : AllocCostModel}
    {A_b : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (A_s A_r : RustAlloc)
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A_b lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PreAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A_r y m i rngPtr sp) :=
  Stage2V1FoldsPlacedBudget.stageP2PreAt_dup_kyberPtr_placed
    (A_s := A_s) (A_r := A_r)
    (spkKit := cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
    (kpkKit := cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
    (pkKit := cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
    (ikit := cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
    y m i w s0 sp fp rngPtr v_a8 v_b8 v_d0
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity

/-- Budget-threaded `stageP2PreAt_dup_kyberPtr_placed` matching the exact output shape of
`Stage2V1FoldsPlacedBudget.stageP2_entry_unpack_pathA_placed` (`A_s := A.atState lim st_b s1` and
`pathAInnerFramePlaced A.repAlloc`). -/
theorem stageP2PreAt_dup_kyberPtr_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} {st_b : M.σ} {s1 : State} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    let A_s : RustAlloc := A.atState lim st_b s1
    stageP2PreAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced A_s
      (cliPollSpkKitPlaced A_s y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A_s y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A_s y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A_s y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) :=
  stageP2PreAt_dup_kyberPtr_placed_ext (A.atState lim st_b s1) A.repAlloc
    y m i w s0 sp fp rngPtr v_a8 v_b8 v_d0

/-- Variant of `stageP2PreAt_dup_kyberPtr_placed` with both outer kits and inner frame at
`A.repAlloc`. -/
theorem stageP2PreAt_dup_kyberPtr_placed_rep {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecPkEnv : DecPkGhost → List AllocEvent → Prop}
    {B : RunBudgets} {S : RunSem} [LibsignalPlacement]
    (y : DpPollGhostStateBudget (dpSlotPollKStatePlaced A lim DecPkEnv B S))
    (m : PreKeyMessageFields) (i : SignalMessage) (w : PathAEntryWords)
    (s0 : State) (sp fp rngPtr v_a8 v_b8 v_d0 : BitVec 64) :
    stageP2PreAtPlaced A.repAlloc
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) ⊢
    ⌜y.g.msgG.kyberPtr ≠ 0#64⌝ ∗
    stageP2PreAtPlaced A.repAlloc
      (cliPollSpkKitPlaced A.repAlloc y.g.F m.spkId (cliKitStk B))
      (cliPollKpkKitPlaced A.repAlloc y.g.F m.kpkId m.spkId y.g.msg.baseKey (cliKitStk B))
      (cliPollPkKitPlaced A.repAlloc y.g.F w.opkWord (cliKitStk B))
      (cliPollIdKitPlaced A.repAlloc y.g.F y.g.peer (cliKitStk B))
      s0 sp fp y.fut y.cx y.out y.g.msgA y.g.msgG.kyberPtr y.g.peerA y.g.meA
      y.g.stores (y.g.stores + 0xc8#64) (y.g.stores + 0x50#64) (y.g.stores + 0x78#64)
      y.g.peerA (y.g.msgA + 0xc8#64) w.u_488 w.u_80 w.u_88 w.u_90 v_a8 v_b8 v_d0
      (mkPathAHdr m) i.messageVersion 0#8 0#8 w.b_4b0 w.b_4f1 0#8
      w.opkWord m.kpkId m.regId m.spkId
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity
      y.g.me y.g.peer (dpClosSubStack B)
      (pathAInnerFramePlaced A.repAlloc y m i rngPtr sp) :=
  stageP2PreAt_dup_kyberPtr_placed_ext A.repAlloc A.repAlloc
    y m i w s0 sp fp rngPtr v_a8 v_b8 v_d0

/-! ## 2. `RustAlloc`-Polymorphic Placed Store Canonicality & Self-Kit Relations -/

theorem cliPollSpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {sid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollSpkKitPlaced A F sid σ).GetErr SignedPreKeyRecord) :
    (cliPollSpkKitPlaced A F sid σ).getEvs id ans = [] := rfl

theorem cliPollKpk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {kid sid id : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (ans : Except (cliPollKpkKitPlaced A F kid sid kbk σ).GetErr KyberPreKeyRecord) :
    (cliPollKpkKitPlaced A F kid sid kbk σ).getEvs id ans = [] := rfl

theorem cliPollPk_getEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid id : BitVec 32} {σ : DpKitStk}
    (ans : Except (cliPollPkKitPlaced A F pid σ).GetErr PreKeyRecord) :
    (cliPollPkKitPlaced A F pid σ).getEvs id ans = [] := rfl

theorem cliPollPk_opkOkEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {pid : BitVec 32} {σ : DpKitStk}
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkEvs (cliPollPkKitPlaced A F pid σ) opt wOpk = [] := by
  cases opt <;> rfl

theorem cliPollPk_opkOkUpdate_placed (A : RustAlloc) [LibsignalPlacement] (F : FsFiles)
    (pid : BitVec 32) (σ : DpKitStk)
    (opt : Option (BitVec 32)) (wOpk : OpkOkWitness opt) :
    opkOkUpdate (cliPollPkKitPlaced A F pid σ) CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime opt wOpk =
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime := by
  cases opt <;> rfl

theorem cliPollSelf_kpEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).KpErr IdentityKeyPair) :
    (cliPollSelfKitPlaced A F peer σ).kpEvs ans = [] := rfl

theorem cliPollSelf_regIdEvs_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk}
    (ans : Except (cliPollSelfKitPlaced A F peer σ).RegIdErr (BitVec 32)) :
    (cliPollSelfKitPlaced A F peer σ).regIdEvs ans = [] := rfl

theorem cliPollSelf_kpRel_ok_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {kp : IdentityKeyPair}
    (h : (cliPollSelfKitPlaced A F peer σ).kpRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.ok kp)) :
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_kpRel_ok_placed
    (A := A) (peer := peer) (σ := σ) h

theorem cliPollSelf_kpRel_err_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKitPlaced A F peer σ).KpErr}
    (h : (cliPollSelfKitPlaced A F peer σ).kpRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.error e)) :
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .error () :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_kpRel_err_placed
    (A := A) (peer := peer) (σ := σ) h

theorem cliPollSelf_regIdRel_ok_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {reg : BitVec 32}
    (h : (cliPollSelfKitPlaced A F peer σ).regIdRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.ok reg)) :
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.regId cliIo.rd F = .ok reg :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_regIdRel_ok_placed
    (A := A) (peer := peer) (σ := σ) h

theorem cliPollSelf_regIdRel_err_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} {e : (cliPollSelfKitPlaced A F peer σ).RegIdErr}
    (h : (cliPollSelfKitPlaced A F peer σ).regIdRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.error e)) :
    CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.regId cliIo.rd F = .error () :=
  CryptoVerification.SignalSession.Cli.RunProofs.Poll.cliPollSelf_regIdRel_err_placed
    (A := A) (peer := peer) (σ := σ) h

/-- Projected Bob private identity key bytes (`UInt8` list of length 32) on Path A. -/
def pathAIkBSk (F : FsFiles) : SignalPqxdh.Bytes :=
  match CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => CryptoVerification.E2E.vecU8 kp₀.privateKey.bytes
  | .error _ => List.replicate 32 0

/-- Projected Bob public identity key bytes (`UInt8` list of length 32) on Path A. -/
def pathAIkBPk (F : FsFiles) : SignalPqxdh.Bytes :=
  match CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F with
  | .ok kp₀ => CryptoVerification.E2E.vecU8 kp₀.identityKey.publicKey.bytes
  | .error _ => List.replicate 32 0

theorem pathAIkBSk_length (F : FsFiles) : (pathAIkBSk F).length = 32 := by
  dsimp only [pathAIkBSk]; split
  · exact vecU8_length _
  · simp

theorem pathAIkBPk_length (F : FsFiles) : (pathAIkBPk F).length = 32 := by
  dsimp only [pathAIkBPk]; split
  · exact vecU8_length _
  · simp

theorem pathAIkBSk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBSk F = CryptoVerification.E2E.vecU8 kp.privateKey.bytes := by
  dsimp only [pathAIkBSk]; rw [h]

theorem pathAIkBPk_of_ok {F : FsFiles} {kp : IdentityKeyPair}
    (h : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp) :
    pathAIkBPk F = CryptoVerification.E2E.vecU8 kp.identityKey.publicKey.bytes := by
  dsimp only [pathAIkBPk]; rw [h]

theorem cliPollSelf_kpRel_sk_eq_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced A F peer σ).kpRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.ok kp)) :
    kp.privateKey.bytes.toList = bytesToBv8 (pathAIkBSk F) := by
  have hkpEq := cliPollSelf_kpRel_ok_placed hrel
  dsimp only [pathAIkBSk]
  rw [hkpEq, bytesToBv8_vecU8]

theorem cliPollSelf_kpRel_pk_eq_placed {A : RustAlloc} [LibsignalPlacement] {F : FsFiles}
    {peer : AddrGhost} {σ : DpKitStk} (kp : IdentityKeyPair)
    (hrel : (cliPollSelfKitPlaced A F peer σ).kpRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity (.ok kp)) :
    kp.identityKey.publicKey.bytes.toList = bytesToBv8 (pathAIkBPk F) := by
  have hkpEq := cliPollSelf_kpRel_ok_placed hrel
  dsimp only [pathAIkBPk]
  rw [hkpEq, bytesToBv8_vecU8]

/-- SPK canonicality (`hspk_wf`) on `cliPollSpkKitPlaced A` under `PreKeyFilesWf`
(`RustAlloc`-polymorphic). -/
theorem cliPollSpk_wf_of_preKeysWf_placed {W : PEParams} {A : RustAlloc} [LibsignalPlacement]
    {F : FsFiles} {spkId : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : SignedPreKeyRecord)
    (hrel : (cliPollSpkKitPlaced A F spkId σ).getRel CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed spkId (.ok r)) :
    ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
      spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
      r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧
      r.signedPreKey.privateKey = spkPrivBytes :=
  cliPollSpk_wf_of_preKeysWf_ext (A := A) (b := 0#64) (σ := σ) hwf r hrel

/-- KPK canonicality (`hkpk_wf`) on `cliPollKpkKitPlaced A` under `PreKeyFilesWf`
(`RustAlloc`-polymorphic). -/
theorem cliPollKpk_wf_of_preKeysWf_placed {W : PEParams} {A : RustAlloc} [LibsignalPlacement]
    {F : FsFiles} {kpkId spkId : BitVec 32} {kbk : PublicKey} {σ : DpKitStk}
    (hwf : PreKeyFilesWf W F)
    (r : KyberPreKeyRecord)
    (hrel : (cliPollKpkKitPlaced A F kpkId spkId kbk σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber kpkId (.ok r)) :
    ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
      kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
      r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
      r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes :=
  cliPollKpk_wf_of_preKeysWf_ext (A := A) (b := 0#64) (spkId := spkId) (kbk := kbk) (σ := σ)
    hwf r hrel

/-- OPK canonicality (`hpk_wf`) on `cliPollPkKitPlaced A` under `PreKeyFilesWf`
(`RustAlloc`-polymorphic). -/
theorem cliPollPk_wf_of_preKeysWf_placed {W : PEParams} {A : RustAlloc} [LibsignalPlacement]
    {F : FsFiles} {opkWord id : BitVec 32} {σ : DpKitStk} (hwf : PreKeyFilesWf W F)
    (r : PreKeyRecord)
    (hrel : (cliPollPkKitPlaced A F opkWord σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime id (.ok r)) :
    ∃ opkPubBytes opkPrivBytes : List (BitVec 8),
      opkPubBytes.length = 32 ∧ opkPrivBytes.length = 32 ∧
      r.preKey.publicKey = 5#8 :: opkPubBytes ∧
      r.preKey.privateKey = opkPrivBytes :=
  cliPollPk_wf_of_preKeysWf_ext (A := A) (b := 0#64) (opkWord := opkWord) (σ := σ) hwf r hrel

/-! ## 3. `RustAlloc`-Polymorphic Placed Pure Path A Model Agreement -/

/-- `PEParams`- and `RustAlloc`-polymorphic placed `pathA_acceptInput_agree` on
`cliPoll*KitPlaced A`. -/
theorem pathA_acceptInput_agree_placed_ext {W : PEParams} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    [LibsignalPlacement] {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)}
    {kp : IdentityKeyPair} {ikBSk ikBPk : SignalPqxdh.Bytes}
    (hdecOk : DecPkOk₀ W Scope F peer me pm)
    (hspkRel : (cliPollSpkKitPlaced A F m.spkId σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKitPlaced A F m.kpkId m.spkId pm.baseKey σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKitPlaced A F opkWord σ)
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkp : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hikBSk : ikBSk = CryptoVerification.E2E.vecU8 kp.privateKey.bytes)
    (hikBPk : ikBPk = CryptoVerification.E2E.vecU8 kp.identityKey.publicKey.bytes) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList ∧
      spkPrivBytes = k.spkPriv.toList ∧
      (∀ reg : BitVec 32,
        mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes =
        ofSignalPqxdhAcceptKeysInput
          (acceptInput W ⟨kp.privateKey.bytes, reg⟩ k m)) :=
  pathA_acceptInput_agree_ext (W := W) (A := A) (b := 0#64) (opkWord := opkWord) (σ := σ)
    hdecOk hspkRel hspkPubEq hspkPrivEq hkpkRel hkpkPubEq hkpkPrivEq
    hopkOk hopkBytes hkp hikBSk hikBPk

/-- `RustAlloc`-polymorphic placed `pathA_acceptInput_agree` on `cliPoll*KitPlaced A` for
`W : CliHooks`. -/
theorem pathA_acceptInput_agree_placed {W : CliHooks} {A : RustAlloc}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    [LibsignalPlacement] {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {m : PreKeyMessageFields} {opkWord : BitVec 32} {σ : DpKitStk}
    {spkRec : SignedPreKeyRecord} {spkPubBytes spkPrivBytes : List (BitVec 8)}
    {kpkRec : KyberPreKeyRecord} {kyberPubBytes kyberPrivBytes : List (BitVec 8)}
    {wOpk : OpkOkWitness (hdrOpkIdBv? (mkPathAHdr m))}
    {opkPkBytes opkSkBytes : List (BitVec 8)}
    {kp : IdentityKeyPair} {ikBSk ikBPk : SignalPqxdh.Bytes}
    (hdecOk : DecPkOk₀ ⟨W.C, W.Q⟩ Scope F peer me pm)
    (hspkRel : (cliPollSpkKitPlaced A F m.spkId σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.signed m.spkId (.ok spkRec))
    (hspkPubEq : spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes)
    (hspkPrivEq : spkRec.signedPreKey.privateKey = spkPrivBytes)
    (hkpkRel : (cliPollKpkKitPlaced A F m.kpkId m.spkId pm.baseKey σ).getRel
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.kyber m.kpkId (.ok kpkRec))
    (hkpkPubEq : kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes)
    (hkpkPrivEq : kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hopkOk : opkOkRel (cliPollPkKitPlaced A F opkWord σ)
      CryptoVerification.SignalSession.Cli.StoresGhost.opened.oneTime (hdrOpkIdBv? (mkPathAHdr m)) wOpk)
    (hopkBytes : opkOkKeyBytes (hdrOpkIdBv? (mkPathAHdr m)) wOpk opkPkBytes opkSkBytes)
    (hkp : CryptoVerification.SignalSession.Cli.StoresGhost.opened.identity.keyPair cliIo.rd F = .ok kp)
    (hikBSk : ikBSk = CryptoVerification.E2E.vecU8 kp.privateKey.bytes)
    (hikBPk : ikBPk = CryptoVerification.E2E.vecU8 kp.identityKey.publicKey.bytes) :
    ∃ k : ResponderPreKeySecrets,
      pkStoreKeys F m = some k ∧
      spkPubBytes = (keyPairOf W.C k.spkPriv).publicKey.bytes.toList ∧
      spkPrivBytes = k.spkPriv.toList ∧
      (∀ reg : BitVec 32,
        mkP2AcceptKeysInput (mkPathAHdr m) ikBSk ikBPk spkPubBytes spkPrivBytes
          kyberPubBytes kyberPrivBytes opkSkBytes =
        ofSignalPqxdhAcceptKeysInput
          (acceptInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, reg⟩ k m)) :=
  pathA_acceptInput_agree_placed_ext hdecOk hspkRel hspkPubEq hspkPrivEq
    hkpkRel hkpkPubEq hkpkPrivEq hopkOk hopkBytes hkp hikBSk hikBPk

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1AgreePlacedBudget
