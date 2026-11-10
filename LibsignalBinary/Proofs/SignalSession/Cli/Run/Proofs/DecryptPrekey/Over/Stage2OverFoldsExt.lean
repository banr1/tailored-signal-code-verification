/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Inst
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchivePromote
import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.MatchCallee
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverFolds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXCli

/-!
# CLI Poll Stage P2 Over-Path (`Path C`) Contract-Backed Callee Folds

Proves the 4 KiB-headroom stack bound (`stageP2OverV1CallStack4K_le_subStack`), the contract-backed
`promote_matching_session` miss and `SessionRecord::promote_state` bridges under `CliExternsOk`, and
`StageP2PathACalleesExt.of_externsOk`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

namespace OverP2Inst

/-! ## 1. 4 KiB-Headroom Stack Budget Bound (`stageP2OverV1CallStack4K`) -/

/-- The 4 KiB-headroom Over-path Stage P2 call-stack budget `stageP2OverV1CallStack4K` instantiated
at the CLI Poll kits fits inside `dpClosSubStack B`. -/
theorem stageP2OverV1CallStack4K_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack4K
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  rw [Over.stageP2OverV1CallStack4K_eq]
  exact stageP2OverV1CallStack_le_subStack b F0 peer spkId kpkId opkIdWord kbk B

/-! ## 2. Contract-Backed `promote_matching_session` Miss & `promote_state` Callee Bridges -/

/-- Universal `PromoteMatchingMissGenPropExt` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliPromoteMatchingMissGenExt_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Over.PromoteMatchingMissGenPropExt A img (cliExternsWith ext) :=
  Over.promoteMatchingMissGen_ext_of_plain
    (subroutine_ok_of_spec_map
      (fun x : Over.P2PromoteMissGhost =>
        (⟨x.recPtr, x.msgVer, x.serPtr, x.serBytes, x.outPtr, x.g, x.r, x.s⟩ :
          Over.PromoteMissGhost))
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (Over.promote_matching_session_miss_ok_ext32 (Slots.ext_blackBox hOk)))

/-- Instance-specialized `PromoteMatchingMissAtPropExt` on `cliExternsWith ext` from
`CliExternsOk P A ext`. -/
theorem cliPromoteMatchingMissAtExt_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8))) (msgVer : BitVec 8) (serBytes : List (BitVec 8))
    (hmiss : ¬ Over.P2SessMatchesMsg sess msgVer serBytes)
    (hlen : serBytes.length = 33) :
    Over.PromoteMatchingMissAtPropExt A img (cliExternsWith ext)
      coroPtr g recG sess msgVer serBytes :=
  Over.promoteMatchingMissAt_of_gen_ext
    (cliPromoteMatchingMissGenExt_ok hOk img)
    coroPtr g recG sess msgVer serBytes hmiss hlen

/-- Universal `PromoteOverGenProp` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliPromoteOverGenExt_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    Over.PromoteOverGenProp A img (cliExternsWith ext) :=
  subroutine_ok_inImage_of_spec_map
    (fun x : Over.P2PromoteOverGenGhost =>
      (⟨x.recPtr, x.src, x.prevCap, x.prevPtr, x.G, x.sess, x.newBs⟩ :
        Over.PromoteOverGenGhost))
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (Over.promote_state_over_gen_ok
      (Store.SerGlueXCli.serContractsX_ext hOk img))

/-- Instance-specialized `PromoteOverAtProp` on `cliExternsWith ext` from `CliExternsOk P A ext`. -/
theorem cliPromoteOverAtExt_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) (img : Obj.Image)
    (coroPtr : BitVec 64) (g : RecordGhost) (recG : SessionGhost)
    (sess : Session (List (BitVec 8)))
    (hlen : (E2E.Record.Serialization.encSessionMem (OverP2.clearPendingGhost recG)
      (OverP2.clearPending sess)).length < 2 ^ 32) :
    Over.PromoteOverAtProp A img (cliExternsWith ext) coroPtr g recG sess :=
  Over.promoteOverAt_of_gen (cliPromoteOverGenExt_ok hOk img) coroPtr g recG sess hlen

end OverP2Inst

/-! ## 3. `StageP2PathACalleesExt` from `CliExternsOk` + `extHookStack ≤ B.readFile` -/

/-- Builds `StageP2PathACalleesExt img P A B ext` from `CliExternsOk P A ext`,
`Obj.Loads libsignalSessionImage img`, `CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile`, and the leaf HKDF/initial-state
contracts (`hext`, `hexp`, `hinit`). -/
theorem StageP2PathACalleesExt.of_externsOk {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {B : RunBudgets} {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (himg : Obj.Loads libsignalSessionImage img)
    (hReadStk : CryptoVerification.LibsignalTripleRatchet.extHookStack ≤ B.readFile)
    (hext : ∀ X, Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hexp : ∀ X, Initiator.PqxdhHkdfExpandMultiInfoOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hinit : CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext)) :
    StageP2PathACalleesExt img P A B ext :=
  StageP2PathACalleesExt.of_pure himg
    (RunHooksExt.of_externsOk hOk img)
    (cliReadFile_ok_cliExternsWith hOk img (hstk := hReadStk))
    (fun X => cliStageP2PureCallees4K_of_hkdf_init X himg hOk (hext X) (hexp X) hinit)
    (fun X => cliInitBobErrOwned4K_ok_ext X himg hOk)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
